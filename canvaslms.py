#!/bin/env python3

##  by Ralf Brown, Carnegie Mellon University
##  last edit: 14aug2019

import argparse
import csv
import datetime
import json
import math
import os
import re
import sys
import urllib, urllib.parse, urllib.request
from urllib.error import HTTPError
from statistics import pstdev, mean  # requires Python 3.4+
from subprocess import call, check_output, CalledProcessError
from time import sleep

######################################################################
####     CONFIGURATION						  ####

API_BASE = "/api/v1/"

## Canvas instances may limit list-returning API calls to as little as 100 entries
MAX_PER_PAGE = 100

######################################################################

class CanvasException(Exception):
    def __init__(self, msg):
        super(CanvasException,self).__init__(msg)

class Grade():
    def __init__(self, points = None, comment = None):
        self.totalpoints = 0.0
        self.comments=[]
        if points is not None:
            self.add(points,comment)
        return

    @staticmethod
    def drop_decimals(value):
        return str(value).replace('.00','').replace('.0','')

    def add(self, points, comment, which=0, penalty = 0):
        for i in range(len(self.comments),which+1):
            self.comments += [None]
        if penalty > 0:
            points = float(points) * (100 - penalty) / 100.0
            if comment is None or comment == '':
                comment = '({}% late penalty)'.format(penalty)
            else:
                comment += ' (less {}% late penalty = {})'.format(penalty,points)
        self.totalpoints += float(points)
        self.comments[which] = comment
        return

    def feedback(self, numparts = 0, possible = 0):
        for i in range(len(self.comments),numparts):
            self.comments += [None]
        for i in range(numparts):
            if self.comments[i] is None:
                self.comments[i] = 'Part {}: not yet submitted'.format(i+1)
        if len(self.comments) > 0:
            if numparts > 1:
                poss = Grade.drop_decimals(possible)
                if int(possible) > 0:
                    self.comments += ['Total: {}/{}'.format(Grade.drop_decimals(self.totalpoints),poss)]
                else:
                    self.comments += ['Total: {}'.format(Grade.drop_decimals(self.totalpoints))]
            if len(''.join(self.comments)) > 0:
                return '\n'.join(self.comments)
        return None

    def percentage(self, possible):
        if possible is None:
            possible = 0
        poss = int(possible)
        if poss > 0:
            perc = int((10000.0 * self.totalpoints / poss) + 0.5)
            return perc / 100.0
        return self.totalpoints

######################################################################

class RubricCriterion():
    def __init__(self, json):
        self.crit_id = json['id']
        self.name = json['description'] if 'description' in json else '(untitled)'
        self.description = json['long_description'] if 'long_description' in json else None
        self.points_possible = json['points'] if 'points' in json else 0.0
        # ratings is an array of dicts with fields 'id', 'points', and 'description'
        self.ratings = json['ratings'] if 'ratings' in json else []
        return

    def display(self, prefix = None):
        if prefix is None:
            prefix = ''
        print('{}{} ({} pts)'.format(prefix,self.name,Grade.drop_decimals(self.points_possible)))
        if self.description:
            print('{}  {}'.format(prefix,self.description))
        for rating in self.ratings:
            print('{}   {}  {}'.format(prefix,Grade.drop_decimals(rating['points']),rating['description']))
        return

######################################################################

class RubricDefinition():
    def __init__(self, json, criteria):
        self.rubric_id = json['id']
        self.title = json['title'] if 'title' in json else '(untitled)'
        self.points_possible = json['points_possible'] if 'points_possible' in json else 0.0
        self.free_form_comments = json['free_form_criterion_comments'] if 'free_form_criterion_comments' in json else False
        self.criteria = [RubricCriterion(crit) for crit in criteria]
        return

    def get_name(self, c_id):
        for crit in self.criteria:
            if crit.crit_id == c_id:
                return crit.name
        return None

    def display(self):
        print('{} ({} pts)'.format(self.title,Grade.drop_decimals(self.points_possible)))
        for crit in self.criteria:
            crit.display('  ')
        return

######################################################################

def latest_rubric_entry(submission):
    if 'rubric_assessment' not in submission:
        print(submission)
        print('* No rubric assessment for',submission['user_id'])
        return None
    rubrics = submission['rubric_assessment']
    if type(rubrics) == type({}):
        return rubrics
    if type(rubrics) is list:
        if len(rubrics) == 1:
            return rubrics[0]
        ## find the rubric_assesement with the latest datestamp
        ##FIXME: we'll assume the last on the list is the most recent
        return rubrics[-1]
    print('Got weird response from Canvas in rubric assessment field:')
    print(rubrics)
    return None

######################################################################

class Course():
    def __init__(self, host, course_name, verbose = False):
        self.token = None		# the API access token
        self.id = None			# the course ID
        self.name = None		# the course name
        self.assignment_id = None
        self.grading_standard = None
        self.verbose = False
        self.dryrun = False
        self.raw_points = False
        self.possible_points = 0	# 0 = use raw points, don't scale to percentage
        self.due_day = 999              # 999 = not specified, assignment will never be considered late
        self.late_percent = 0		# percent per day late
        self.max_late = 100		# maximum days late allowed
        self.target_mean = 85		# target mean score for curving
        self.target_stddev = 5		# standard deviation of curved scores in percentage points
        self.hostname = host
        self.api_base = 'https://'+ self.hostname + API_BASE
        self.user_base = 'https://' + self.hostname
        self.http_error_hook = None
        self.cached_roster = None
        self.cached_drops = None
        self.cached_enrollments = None
        self.cached_submissions = None
        self.cached_assignment_id = None
        self.cached_reviews = None
        self.cached_reviews_assignment = None
        tokenfile = os.environ['HOME'] + '/.canvas_api_token'
        try:
            with open(tokenfile) as f:
                self.token = f.read().strip()
        except Exception as err:
            print(err)
            return
        courses = self.get('courses',[],True)
        if courses == []:
            print('Unable to establish connection to server.  Goodbye....')
            quit()
        start = '0000-00-00'
        # find the most recent iteration of the named course
        for c in courses:
            if 'name' in c and c['name'] == course_name and ('start_at' not in c or c['start_at'] > start):
                self.id = c['id']
                self.name = c['name']
                if 'start_at' in c:
                    start = c['start_at']
        if course_name and self.id is None:
            print('Requested course '+course_name+' not found.  Goodbye....')
            quit()
        self.run_verbosely(verbose)
        return

    def run_verbosely(self, verbosity):
        self.verbose = verbosity
        return

    def mail_address(self, mail):
        self.mail = mail
        return
    
    def simulate(self, sim):
        self.dryrun = sim
        return

    def use_raw_points(self, use_raw = True):
        self.raw_points = use_raw
        return

    def set_points(self, points):
        self.possible_points = points
        return

    def set_late_percentage(self, percent_per_day, max_days_late):
        self.late_percent = percent_per_day
        self.max_late = max_days_late
        return

    def set_due_day(self, day_in_year):
        if day_in_year is None:
            day_in_year = 999	# not specified, assignment will never be considered late
        self.due_day = day_in_year
        return

    def days_late(self,submit_date):
        submit_date = self.day_of_year(Course.normalize_date(submit_date))
        late = submit_date - self.due_day
        if late < 0:
            return 0
        return late

    def late_penalty_by_days(self,late):
        if late > 0:
            if late > self.max_late:
                return 100
            return late * self.late_percent
        return 0

    def late_penalty(self,submit_date):
        late = self.days_late(submit_date)
        return self.late_penalty_by_days(late)

    ## staffeli/canvas.py showed how to call API
    def mkrequest(self, method, url, arglist, use_JSON_data):
        # convert a relative URL into an absolute URL by appending it to the base URL for the API
        if '://' not in url:
            url = self.api_base + url
        if arglist is None:
            arglist = []
        headers = { 'Authorization': 'Bearer ' + self.token }
        if use_JSON_data:
            if type(arglist) is type(''):
                qstring = ''.join(c if c != '\n' else ' ' for c in arglist)
            else:
                qstring = json.dumps(arglist)
            qstring = qstring.encode('utf-8')
            headers['Content-Type'] = 'application/json'
        else:
            # add page-size to request
            arglist = arglist + [('per_page',MAX_PER_PAGE)]  ## be sure to leave original list intact
            qstring = urllib.parse.urlencode(arglist, safe='[]@', doseq=True).encode('utf-8')
        #if self.verbose and (len(arglist) > 1 or use_JSON_data):
        #    print("Encoded args:",qstring)
        return urllib.request.Request(url, data=qstring, method=method, headers=headers)

    ## staffeli/canvas.py showed how to call API
    def extract_next_link(self, f):
        # grab Link header, which is a comma-separated list, and split it up
        link_header = f.info()['Link']
        if link_header:
            links = link_header.split(',')
            # each link is a URL followed by ' ;rel="XX"', where XX=current/next/first/last
            urls = {rel[:-1]: link[1:-1] for link, rel in (s.split('; rel="') for s in links) }
            if 'last' in urls and urls['current'] != urls['last']:
                return urls['next']
            elif 'next' in urls:
                return urls['next']
        return None
        
    ## staffeli/canvas.py showed how to call API
    def call_api(self, method, url, arglist, all_pages=False, use_JSON_data=False):
        if arglist is None:
            arglist = []
        entries = []
        while url:
            request = self.mkrequest(method, url, arglist, use_JSON_data)
            with urllib.request.urlopen(request) as f:
                if f.getcode() == 204:  # No Content
                    break
                data = json.loads(f.read().decode('utf-8'))
                if type(data) is list:
                    entries.extend(data)
                else:
                    entries.append(data)
                url = self.extract_next_link(f)
                if not all_pages:
                    url = None
        return entries

    def get(self,url,arglist=None,all_pages=False):
        try:
            result = self.call_api('GET', url, arglist, all_pages)
        except HTTPError as err:
            if self.http_error_hook:
                self.http_error_hook(err)
            else:
                print(err,'for GET',url)
            result = []
        return result

    def put(self,url,arglist=[], use_JSON_data=False):
        if self.dryrun:
            print('DRY RUN: would have PUT',url,'with args:\n',arglist)
            return []
        try:
            return self.call_api('PUT', url, arglist, use_JSON_data=use_JSON_data)
        except HTTPError as err:
            print(err,'for PUT',url)

    def post(self,url,arglist=[], use_JSON_data=False):
        if self.dryrun:
            print('DRY RUN: would have POSTed',url,'with args:\n',arglist)
            return []
        try:
            return self.call_api('POST', url, arglist, use_JSON_data=use_JSON_data)
        except HTTPError as err:
            print(err,'for POST',url)

    def patch(self,url,arglist=[]):
        if self.dryrun:
            print('DRY RUN: would have PATCHed',url,'with args:\n',arglist)
            return []
        try:
            return self.call_api('PATCH', url, arglist)
        except HTTPError as err:
            print(err,'for PATCH',url)

    def delete(self,url,arglist=[]):
        if self.dryrun:
            print('DRY RUN: would have DELETEd',url,'with args:\n',arglist)
            return []
        try:
            return self.call_api('DELETE', url, arglist)
        except HTTPError as err:
            print(err,'for DELETE',url)

    def active_uids(self, student_ids):
        if student_ids is None:
            student_ids = self.fetch_active_students()
        uids = { id:email for (email, id) in student_ids.items() }
        return uids

    def whoami(self):
        me = self.get('users/self')
        if len(me) > 0:
            me = me[0]
        if 'name' in me:
            return me['name']
        return 'Not authenticated'

    def student_name(self, uid):
        '''
        retrieve the student name from the given user ID
        '''
        for student in self.fetch_roster():
            if student['id'] == uid:
                if 'name' in student:
                    return student['name']
                else:
                    return None
        return None

    def student_email(self, uid):
        '''
        retrieve the student login/email address from the given user ID
        '''
        ids = self.fetch_active_students()
        if ids:
            for email, user_id in ids.items():
                if user_id == uid or -user_id == uid:
                    return email
        return "(unknown)"

    def student_login(self, uid):
        '''
        retrieve the student login from the given user ID
        '''
        email = self.student_email(uid)
        if self.mail in email:
            login, m, rest = email.rpartition(self.mail)
            return login
        return email

    def get_id_for_student(self, login):
        '''
        get the user ID corresponding to the given student login/email address
        '''
        if login is None:
            return None
        if type(login) is str:
            login = login.lower()
        if '@' not in login:
            login = login + self.mail
        ids = self.fetch_active_students()
        if login in ids:
            return ids[login]
        return None

    def get_student_id(self, login1, login2 = None):
        id = self.get_id_for_student(login1)
        if id is None and login2 is not None:
            id = self.get_id_for_student(login2)
        if id is None:
            if login2:
                print('*',login1,"("+str(login2)+") not on roster")
            else:
                print('*',login1,"not on roster")
        if type(id) is int and id < 0:
            if login2:
                print('-',login1,"("+str(login2)+") has dropped")
            else:
                print('-',login1,"has dropped")
            id = None
        return id

    def active_grading_standard_id(self):
        if self.grading_standard is None:
            # we haven't cached the grading standard ID yet, so fetch it
            course_info = self.get('courses/{}'.format(self.id),[],True)
            if type(course_info) is list:
                course_info = course_info[0]
            if 'grading_standard_id' in course_info:
                self.grading_standard = int(course_info['grading_standard_id'])
        return self.grading_standard

    def clear_submissions_cache(self):
        self.cached_submissions = None
        self.cached_assignment_id = None
        return

    @staticmethod
    def compute_split_stddev(values):
        if values is None or len(values) < 2:
            return 0.0, 0.0
        avg = mean(values)
        upper = sum((x-avg)*(x-avg) for x in values if x >= avg)
        num_upper = sum(1 for x in values if x >= avg)
        lower = sum((x-avg)*(x-avg) for x in values if x <= avg)
        num_lower = sum(1 for x in values if x <= avg)
        upper_stdev = 0.0 if num_upper < 1 else math.sqrt(upper / num_upper)
        lower_stdev = 0.0 if num_lower < 2 else math.sqrt(lower / num_lower)
        return upper_stdev, lower_stdev
    
        
    def compute_threshold(self, mean, upper_stddev, lower_stddev, devs):
        if devs < 0:
            if mean + devs * lower_stddev < 5:
                thresh = (mean - 5) / lower_stddev
                return 5 * (1 + (thresh + devs) / thresh)
            stddev = lower_stddev
        else:
            up_devs = (100 - self.target_mean) / self.target_stddev
            if mean + up_devs * upper_stddev > 100:
                upper_stddev = (100 - mean) / up_devs
            stddev = upper_stddev
        return mean + ( devs * stddev )

    def compute_curve(self, standard, split_stddev = True, pass_devs = None):
        grades = self.fetch_running_grades()
        if len(grades) == 0:
            print("No grades yet")
            return None
        if standard is None:
            standard = [('A+',2.4,97),('A',1.8,94),('A-',1.0,90),
                        ('B+',0.4,87),('B',-0.2,84),('B-',-1.0,80),
                        ('C+',-1.6,77),('C',-2.2,74),('C-',-3.0,70),
                        ('D+',-3.6,67),('D',-4.2,64),('D-',-4.8,60)]
        mean = sum(grades) / len(grades)
        print('Mean: {:.3f}'.format(mean))
        if split_stddev:
            upper_stddev, lower_stddev = Course.compute_split_stddev(grades)
            print('StdDev: +{:.3f}/-{:.3f}'.format(upper_stddev,lower_stddev))
        else:
            upper_stddev = pstdev(grades)
            lower_stddev = upper_stddev
            print('StdDev: {:.3f}'.format(upper_stddev))
        scheme = []
        i = 0
        for (letter, devs, std) in standard:
            threshold = self.compute_threshold(mean,upper_stddev,lower_stddev,devs)
            if threshold > std:
                threshold = std
            print('{:2s} = {:.3f}'.format(letter,threshold))
            scheme += [('grading_scheme_entry[][name]',letter),('grading_scheme_entry[][value]',threshold)]
        scheme += [('grading_scheme_entry[][name]','F'),('grading_scheme_entry[][value]',0.0)]
        if pass_devs is not None:
            print('Pass: {:.3f}'.format(self.compute_threshold(mean,upper_stddev,lower_stddev,pass_devs)))
        return scheme

    def current_grading_standard(self):
        standards = self.fetch_grading_standards()
        for st in standards:
            if 'id' in st and st['id'] == self.active_grading_standard_id():
                return st
        return None

    def find_assignment_id(self, name):
        if self.verbose:
            print("Finding assignment ID by name:",name)
        if (name == "None"):
            return None
        assign_id = None
        matches = self.fetch_assignments(name)
        if matches is None or len(matches) == 0:
            if name is None:
                print("No assignments for course")
            else:
                print(name,'does not match any assignments')
        if len(matches) == 1:
            _, assign_id = list(matches.items())[0]
        elif name in matches:
            assign_id = matches[name]
            print("Found exact match for '",name,"', but there are additional partial matches",sep='')
        elif name is not None and len(matches) > 1:
            print(name,'is ambiguous, and matches:')
            for name in matches:
                print('  ',name)
        if self.verbose:
            print("Assignment ID:",assign_id)
        return assign_id
        
    def find_assignment(self, name):
        self.assignment_id = self.find_assignment_id(name)
        return
        
    def find_quiz_id(self, name):
        if self.verbose:
            print("Finding quiz ID by name:",name)
        quiz_id = None
        matches = self.fetch_quizzes(name)
        if matches is None or len(matches) == 0:
            if name is None:
                print("No quizzes for course")
            else:
                print(name,'does not match any quizzes')
        if len(matches) == 1:
            _, quiz_id = list(matches.items())[0]
        elif name in matches:
            quiz_id = matches[name]
            print("Found exact match for '",name,"', but there are additional partial matches",sep='')
        elif name is not None and len(matches) > 1:
            print(name,'is ambiguous, and matches:')
            for name in matches:
                print('  ',name)
        if self.verbose:
            print("Quiz ID:",quiz_id)
        return quiz_id
        
    def find_quiz(self, name):
        self.quiz_id = self.find_quiz_id(name)
        return
        
    def fetch_active_students(self):
        student_ids = {}
        for student in self.fetch_roster():
            student_ids[student['login_id']] = student['id']
        return student_ids

    def fetch_activity_stream(self, user_id = None, all_pages = False):
        if user_id is None:
            user_id = 'self'
        return self.get('users/{}/activity_stream'.format(user_id),[],all_pages)

    def fetch_activity_stream_summary(self, user_id = None):
        if user_id is None:
            user_id = 'self'
        return self.get('users/{}/activity_stream/summary'.format(user_id))

    def fetch_assignments(self, name = None):
        if self.verbose:
            print("Fetching list of assignments")
        arglist = []
        if name is not None:
            arglist += [('search_term',name)]
        assignments = self.get('courses/{}/assignments'.format(self.id),arglist,True)
        assign_ids = {}
        for a in assignments:
            name = a['name']
            aid = a['id']
            assign_ids[name] = aid
        return assign_ids

    def fetch_assignment_grades(self,assign_id = None):
        '''
        returns a dict of uid:grade for the selected assignment
        '''
        if self.verbose:
            print("Fetching grades for assignment")
        grades = {}
        subs = self.fetch_submissions(assign_id)
        for sub in subs:
            uid = int(sub['user_id'])
            grade = -9999
            if 'entered_grade' in sub and sub['entered_grade'] is not None:
                try:
                    grade = float(sub['entered_grade'])
                except:
                    if sub['entered_grade'] == 'EX':
                        grade = 'EX'
            grades[uid] = grade
        return grades

    def fetch_assignment_submissions(self, assign_id = None, arglist = None):
        if assign_id is None:
            assign_id = self.assignment_id
        if arglist is None:
            arglist = []
        return self.get('courses/{}/assignments/{}/submissions'.format(self.id,assign_id),arglist,True)

    def fetch_courses(self,student_count,concluded):
        arglist=[]
        if student_count:
            arglist.append(('include[]','total_students'))
        if concluded:
            arglist.append(('include[]','concluded'))
        return self.get('courses',arglist=arglist)

    def fetch_dashboard_positions(self,user_id = None):
        if user_id is None:
            user_id = 'self'
        return self.get('users/{}/dashboard_positions'.format(user_id))

    def fetch_drops(self):
        if self.cached_drops is None:
            if self.verbose:
                print("Fetching dropped students")
            arglist = [('enrollment_state[]','completed'),('enrollment_type[]','student')]
            self.cached_drops = self.get('courses/{}/users'.format(self.id),arglist,True)
        return self.cached_drops

    def fetch_enrollments(self):
        if self.cached_enrollments is None:
            if self.verbose:
                print("Fetching current roster")
            arglist = [('state','active'),('type','StudentEnrollment')]
            self.cached_enrollments = self.get('courses/{}/enrollments'.format(self.id),arglist,True)
        return self.cached_enrollments
        
    def fetch_graded(self, student_ids = None):
        '''
        returns a list of student ids for which a grade has already been entered for the current assignment
        '''
        graded = {}
        if self.assignment_id is not None:
            uids = self.active_uids(student_ids)
            grades = self.fetch_assignment_grades()
            graded = { uid: uids[uid] for uid, grade in grades.items() if grade > -9999 and uid in uids }
        return graded

    def fetch_grading_standards(self):
        return self.get('courses/{}/grading_standards'.format(self.id),[],True)

    def fetch_incomplete(self, student_ids = None):
        '''
        returns a list of student ids for which the comment text indicates one or more parts of the assignment are
        currently missing
        '''
        incomplete = {}
        if self.assignment_id is None:
            return {}
        uids = self.active_uids(student_ids)
        subs = self.fetch_submissions(include_comments=True)
        for sub in subs:
            uid = int(sub['user_id'])
            if uid in uids:
                pass  ##FIXME
        return incomplete

    def fetch_observees(self,uid,include_avatar=False):
        arglist = []
        if include_avatar:
            arglist += [('include','avatar_url')]
        return self.get('users/{}/observees'.format(uid),arglist,True)

    def fetch_quizzes(self, name = None):
        if self.verbose:
            print("Fetching list of quizzes")
        arglist = []
        if name is not None:
            arglist += [('search_term',name)]
        quizzes = self.get('courses/{}/quizzes'.format(self.id),arglist,True)
        quiz_ids = {}
        for q in quizzes:
            name = q['title']
            qid = q['id']
            quiz_ids[name] = qid
        return quiz_ids

    def fetch_quiz_submissions(self):
        if self.verbose:
            print("Fetching list of quiz submissions")
        arglist = [('include[]','submission')]
        submissions = self.get('/courses/{}/quizzes/{}/submissions'.format(self.id,self.quiz.id),arglist)
        return submissions

    def fetch_reviews(self, assign_id = None, terse = False):
        if assign_id is None:
            assign_id = self.assignment_id
        if assign_id is None:
            return []
        if self.cached_reviews_assignment != assign_id or self.cached_reviews is None:
            if self.verbose:
                print('Fetching reviews for assignment',assign_id)
            arglist = [] if terse else [('include',['submission_comments','user'])]
            self.cached_reviews = self.get('courses/{}/assignments/{}/peer_reviews'.format(self.id,assign_id),
                                           arglist,True)
        return self.cached_reviews

    def fetch_roster(self):
        if self.cached_roster is None:
            if self.verbose:
                print("Fetching current roster")
            arglist = [('enrollment_state[]','active'),('enrollment_type[]','student')]
            self.cached_roster = self.get('courses/{}/users'.format(self.id),arglist,True)
        return self.cached_roster
        
    def fetch_rubric(self, id, which='assessments', full=True):
        if self.verbose:
            print("Fetching details of rubric",id)
        arglist = [('include',which)]
        if full:
            arglist.append(('style','full'))
        return self.get('courses/{}/rubrics/{}'.format(self.id,id),arglist)
        
    def fetch_rubrics(self):
        if self.verbose:
            print("Fetching active rubrics")
        return self.get('courses/{}/rubrics'.format(self.id),[],True)

    def fetch_rubric_def(self, assign_id = None):
        if assign_id is None:
            assign_id = self.assignment_id
        if self.verbose:
            print('Fetching info for assignment',assign_id)
        assign_info = self.get('courses/{}/assignments/{}'.format(self.id,assign_id))
        if type(assign_info) is list and len(assign_info) > 0:
            assign_info = assign_info[0]
        if 'rubric_settings' not in assign_info or 'rubric' not in assign_info:
            return None
        return RubricDefinition(assign_info['rubric_settings'],assign_info['rubric'])

    def fetch_running_grades(self):
        grades = []
        enrollments = self.fetch_enrollments()
        for enrollment in enrollments:
            if 'grades' not in enrollment:
                continue
            gr = enrollment['grades']
            if 'current_score' in gr and gr['current_score'] is not None:
                grades += [gr['current_score']]
        return grades

    def fetch_students(self):
        student_ids = {}
        for student in self.fetch_roster():
            student_ids[student['login_id']] = student['id']
        for student in self.fetch_drops:
            student_ids[student['login_id']] = -student['id']
        return student_ids

    def fetch_submissions(self, assign_id = None, include_comments = False, include_rubric = False):
        if assign_id is None:
            assign_id = self.assignment_id
        if self.cached_assignment_id == assign_id and self.cached_submissions is not None:
            return self.cached_submissions
        if self.verbose:
            print("Fetching submissions for assignment")
        self.cached_assignment_id = assign_id
        arglist = [('student_ids','all'), ('assignment_ids',assign_id)]
        if include_comments:
            arglist.append(('include[]','submission_comments'))
        if include_rubric:
            arglist.append(('include[]','rubric_assessment'))
        self.cached_submissions = self.get('courses/{}/students/submissions'.format(self.id),arglist,True)
        return self.cached_submissions

    def fetch_tabs(self,include_external=False):
        arglist = []
        if include_external:
            arglist += [('external',True)]
        return self.get('courses/{}/tabs'.format(self.id),arglist,True)

    def fetch_todo(self, user_id = None):
        if user_id is None:
            user_id = 'self'
        if self.verbose:
            print("Fetching TODO list")
        return self.get('users/{}/todo'.format(user_id))

    def fetch_ungraded(self, student_ids = None):
        '''
        returns a list of student ids for which no grade has been entered for the current assignment yet
        '''
        if self.verbose:
            print('Fetching ungraded submissions')
        ungraded = {}
        if self.assignment_id is not None:
            uids = self.active_uids(student_ids)
            grades = self.fetch_assignment_grades()
            ungraded = { uid: uids[uid] for uid, grade in grades.items() if grade == -9999 and uid in uids }
        if self.verbose:
            print(' ',ungraded)
        return ungraded

    def fetch_upcoming(self,user_id = None):
        if user_id is None:
            user_id = 'self'
        if self.verbose:
            print("Fetching upcoming calendar items")
        return self.get('users/{}/upcoming_events'.format(user_id))

    def set_tab_position(self, tab_id, position):
        if self.verbose:
            print("Setting position of tab",tab_id,"to",position)
        arglist = [('position',position)]
        tab = self.put('courses/{}/tabs/{}'.format(self.id,tab_id),arglist)
        return tab

    def set_tab_visibility(self, tab_id, visible):
        if self.verbose:
            print("Setting visibility of tab",tab_id,"to",visible)
        arglist = [('hidden',not visible)]
        tab = self.put('courses/{}/tabs/{}'.format(self.id,tab_id),arglist)
        return tab

    # originally adapted from staffeli/cli.py
    def upload_grade(self, user_id, grade, message):
        arglist = [("submission[posted_grade]", grade)]
        if message:
            arglist += [("comment[text_comment]", message), ("comment[group_comment]", True)]
        if self.dryrun:
            print('simulating grade upload:',user_id,arglist)
            return
        resp = self.put('courses/{}/assignments/{}/submissions/{}'.format(self.id, self.assignment_id, user_id),
                        arglist)
        if 'grade' not in resp:
            raise CanvasException("Expected a response showing the new grade, got:\n{}".format(resp))
        self.clear_submissions_cache()
        return

    def batch_upload_grades(self, grades, numparts = 1, assign_id = None):
        '''
        upload grades and associated comments for a set of students.  If 'numparts' is zero, upload only comments.
        'grades' is a map from Canvas uids to any of: Grade() instance, int/float score, or list of (score,message)
        '''
        arglist = []
        prev_grades = self.fetch_assignment_grades(assign_id)
        emails = None
        student_ids = self.fetch_active_students()
        for uid in grades:
            gr = grades[uid]
            if gr is None:
                continue
            feedback = None
            if type(gr) is int or type(gr) is float:
                gr = Grade(gr,'')
            elif type(gr) is list or type(gr) is tuple:
                feedback = gr[1]
                gr = Grade(gr[0],gr[1])
            if numparts == 0:
                grade = None
                possible = 0
            elif self.raw_points or self.possible_points == 0 or assign_id:
                grade = gr.totalpoints
                possible = 0
            else:
                grade = gr.percentage(self.possible_points)
                possible = self.possible_points
            if uid in prev_grades and grade is not None and grade <= prev_grades[uid]:
                if not emails:
                    emails = self.active_uids(student_ids)
                if uid in emails:
                    name = emails[uid]
                else:
                    name = uid
                if grade < prev_grades[uid]:
                    print('*',name,'decreased from',prev_grades[uid],'to',grade,'(skipping update)')
                elif self.verbose:
                    print('- skipping',name,'because grade has not changed')
                continue
            if not feedback:
                feedback = gr.feedback(numparts,possible)
            if self.verbose:
                print('will upload',uid,grade,feedback)
            if numparts > 0 and grade is not None:
                arglist += [('grade_data[{}][posted_grade]'.format(uid),grade)]
            if feedback and feedback != '':
                arglist += [('grade_data[{}][text_comment]'.format(uid),feedback),
                            ('grade_data[{}][group_comment]'.format(uid),True)]
        if arglist == []:
            print('No grades to upload\n')
            return
        if assign_id is None:
            assign_id = self.assignment_id
        url = 'courses/{}/assignments/{}/submissions/update_grades'.format(self.id,assign_id)
        try:
            resp = self.post(url,arglist)
            if self.dryrun:
                return
            if self.verbose:
                print('upload command sent')
        except HTTPError as err:
            print(err,'for',url)
            resp = [{'url': None, 'workflow_state':'skipped'}]
        if type(resp) is not list or 'url' not in resp[0]:
            raise CanvasException("Canvas response looks weird: {}".format(resp))
        resp = resp[0]
        url = resp['url']
        print('Waiting for grade upload to be processed',end='',flush=True)
        while url and resp['workflow_state'] in  ['queued','running']:
            sleep(1)
            print('.',end='',flush=True)
            resp = self.get(resp['url'])
            if type(resp) is list:
                resp = resp[0]
            if 'workflow_state' in resp and resp['workflow_state'] == 'completed':
                break
            if 'url' not in resp:
                break
            url = resp['url']
        print('')
        print('status =',resp['workflow_state'])
        self.clear_submissions_cache()
        return

    def peer_review_user_link(self, assign_id, reviewee_uid):
        if reviewee_uid is None or reviewee_uid < 0:
            return ''
        if assign_id is None:
            assign_id = self.assignment_id
        return '{}/courses/{}/assignments/{}/submissions/{}'.format(self.user_base,self.id,assign_id,reviewee_uid)
        
    def add_peer_reviewer_to_submission(self, assign_id, submission_id, reviewer_uid):
        arg_list = [('user_id[]',reviewer_uid)]
        self.post('courses/{}/assignments/{}/submissions/{}/peer_reviews'.format(self.id,assign_id,submission_id),
                  arg_list)
        return

    def remove_peer_reviewer_from_submission(self, assign_id, submission_id, reviewer_uids):
        if reviewer_uids is None or reviewer_uids == []:
            return
        if type(reviewer_uids) is int:
            arg_list = [('user_id[]',reviewer_uids)]
        else:
            arg_list = [('user_id[]',uid) for uid in reviewer_uids]
        self.delete('courses/{}/assignments/{}/submissions/{}/peer_reviews'.format(self.id,assign_id,submission_id),
                    arg_list)
        return

    def find_student_submission(self, submissions, student_uid):
        sub_id = None
        for sub in submissions:
            if 'user_id' in sub and sub['user_id'] == student_uid:
                sub_id = sub['id']
                break
        return sub_id

    def add_peer_reviewer(self, student_login, reviewer_login, assign_id = None):
        if assign_id == None:
            assign_id = self.assignment_id
        student_ids = self.fetch_active_students()
        uid = self.get_student_id(student_login)
        reviewer_uid = self.get_student_id(reviewer_login)
        if uid is not None and uid > 0 and reviewer_uid is not None and reviewer_uid > 0:
            submissions = self.fetch_assignment_submissions(assign_id)
            sub_id = self.find_student_submission(submissions,uid)
            if sub_id is None:
                print('No entry found for',student_login,'in assignment',assign_id)
                return
            self.add_peer_reviewer_to_submission(assign_id, sub_id, reviewer_uid)
        return

    def add_peer_reviewers(self, reviewer_map, assign_id = None):
        '''
        given a map of student->reviewer, add a peer review to each student submission for the assignment
        '''
        if assign_id == None:
            assign_id = self.assignment_id
        student_ids = self.fetch_active_students()
        submissions = self.fetch_assignment_submissions(assign_id)
        if not self.verbose:
            print('Assigning peer reviews',end='',flush=True)
        for student, reviewer in reviewer_map.items():
            student_uid = self.get_student_id(student)
            reviewer_uid = self.get_student_id(reviewer)
            if student_uid is None or student_uid < 0 or reviewer_uid is None or reviewer_uid < 0:
                continue
            if self.verbose:
                print('Assigning peer review: {} ({}) -> {} ({})'.format(reviewer,reviewer_uid,student,student_uid))
            else:
                print('.',end='',flush=True)
            sub_id = self.find_student_submission(submissions,student_uid)
            if sub_id is None:
                print('No entry found for',student,'in assignment',assign_id)
            else:
                self.add_peer_reviewer_to_submission(assign_id, sub_id, reviewer_uid)
        if not self.verbose:
            print('')
        return

    def find_peer_reviewers(self, uid, reviews):
        reviewers = []
        for review in reviews:
            if review['user'] and review['user']['id'] == uid and review['assessor'] \
                   and review['workflow_state'] == 'assigned':
                reviewers.append(review['assessor']['id'])
        if self.verbose:
            print('peer reviewers for',uid,'are',reviewers)
        return reviewers

    def remove_peer_reviewers(self, students, assign_id = None):
        '''
        given a list of students, remove any existing peer review from the student submission for the assignment
        '''
        if assign_id == None:
            assign_id = self.assignment_id
        student_ids = self.fetch_active_students()
        submissions = self.fetch_assignment_submissions(assign_id)
        reviews = self.fetch_reviews(assign_id)
        if not self.verbose:
            print('Removing peer reviews',end='',flush=True)
        for student in students:
            if type(student) is int:
                student_uid = student
                student = self.student_email(student_uid)
            else:
                student_uid = self.get_student_id(student)
            if student_uid is None or student_uid < 0:
                continue  ## unknown or dropped student
            if self.verbose:
                print('Removing peer review from {} ({})'.format(student,student_uid))
            else:
                print('.',end='',flush=True)
            sub_id = self.find_student_submission(submissions,student_uid)
            if sub_id is None:
                print('No entry found for',student,'in assignment',assign_id)
            else:
                reviewers = self.find_peer_reviewers(student_uid,reviews)
                self.remove_peer_reviewer_from_submission(assign_id, sub_id, reviewers)
        if not self.verbose:
            print('')
        return

    @staticmethod
    def check_rubric_complete(rubric):
        for crit in rubric:
            if 'points' not in crit:
                ## allow a blank comment-only entry
                if 'description' in crit and 'comment' in crit['description']:
                    continue
                return False
        return True

    @staticmethod
    def copy_rubric_score_to_grade(submissions, rubric_def, rubric_grades, submit_grades, assessors, submit_points,
                                   course, verbose = False, require_complete = False):
        for sub in submissions:
            if sub['id'] not in assessors:
                continue
            uid = sub['user_id']
            reviewer, total_points, data = assessors[sub['id']]
            if reviewer == uid:
                print('! self-assessment for {}'.format(course.student_login(uid)))
                continue
            if total_points == 0:
                email = course.student_login(uid)
                print('! {} ({}) received a zero score'.format(email,uid))
            incomplete = require_complete and not Course.check_rubric_complete(data)
            if incomplete:
                print('! Incomplete rubric by {} for {}'.format(course.student_login(reviewer),course.student_login(uid)))
                submit_grades[reviewer] = Grade(submit_points/2,"Incomplete rubric")
            else:
                rubric_grades[uid] = total_points
                submit_grades[reviewer] = submit_points
            if verbose:
                print(course.student_login(reviewer),'entered',total_points,'for',course.student_login(uid))
        return

    @staticmethod
    def clamp(val, limit):
        if val and limit > 0 and val > limit:
            val = limit
        return val

    def confirm_peer_review_scores(self, review_assign_id = None, submit_assign_id = None,
                                   parse_func = None, submit_points = 10, require_complete = False):
        '''
        Assign the score from a peer review as the grade for the assignment, and optionally assign
        full marks to another assignment for making the peer review.  If parse_func is given, call
        it to convert rubric scores into grades, otherwise just copy the total rubric score as the grade
        '''
        if review_assign_id is None:
            review_assign_id = self.assignment_id
        # get both current and former students, since someone may have filled out a rubric before dropping the course
        student_ids = self.fetch_students()
        # fetch the assignment description,which embeds the rubric, and extract the rubric definition
        rubric_def = self.fetch_rubric_def(review_assign_id)
        if rubric_def is None:
            print('** No rubric associated with assignment **')
            return
        # fetch the info for the rubric associated with the assignment and extract assessments
        if self.verbose:
            print('rubric_id:',rubric_def.rubric_id)
        rubric_type = 'assessments' if submit_assign_id is None else 'peer_assessments' ;
        rubric_info = self.fetch_rubric(rubric_def.rubric_id,rubric_type,(parse_func != None or require_complete))
        if type(rubric_info) is list:
            rubric_info = rubric_info[0]
        if self.verbose:
            print('======== RUBRIC INFO =========')
            print(rubric_info)
            print('======== END RUBRIC =========')
        points_possible = rubric_info['points_possible'] if 'points_possible' in rubric_info else 0
        peer_reviews = self.fetch_reviews(review_assign_id)
        ## fetch all submissions, including the rubric_assessment  BUG: doesn't work for peer reviews!
        #arglist = [('include[]','rubric_assessments')]
        arglist = [('include[]','assessments')]
        arglist = [('include[]','submission_comments')]
        submissions = self.fetch_assignment_submissions(review_assign_id,arglist)
        #if self.verbose:
        #    print('============ SUBMISSIONS ============')
        #    print(submissions)
        #    print('============ END SUBMISSIONS ============')
        rubric_grades = {}	# map from uid to score earned from rubric
        submit_grades = {}	# map from uid to score for submitting peer_review
        assessors = {}		# map from submission_id to uid for assessor
        if rubric_info is not None and 'assessments' in rubric_info:
            ## collect assessors and scores off of peer reviews
            if self.verbose:
                assessors = { a['artifact_id'] : (a['assessor_id'], a['score']) for a in rubric_info['assessments'] }
                print('ASSESSORS:',assessors)
            assessors = { a['artifact_id'] : (a['assessor_id'], Course.clamp(a['score'],points_possible),
                                              a['data'] if 'data' in a else None) \
                          for a in rubric_info['assessments'] }
        if parse_func is None:
            parse_func = self.copy_rubric_score_to_grade
        parse_func(submissions,rubric_def,rubric_grades,submit_grades,assessors,submit_points,self,self.verbose,
                   require_complete)
        print('')
        print('Uploading rubric grades')
        try:
            self.batch_upload_grades(rubric_grades,1)
        except CanvasException as err:
            print(err)
            return
        if submit_assign_id:
            print('')
            print('Uploading grades for submitting peer review')
            try:
                self.batch_upload_grades(submit_grades,1,submit_assign_id)
            except CanvasException as err:
                print(err)
        return

    def make_curve(self, standard, split_stddev = True, verbose = False, dryrun = True, pass_devs = -2.0):
        '''
        Compute the curve that maps the current class performance to the given grading standard,
        then upload it to Canvas as a new Grading Standard named "Curved Grading YYYY-MM-DD"
        '''
        self.simulate(dryrun)
        scheme = self.compute_curve(standard,split_stddev,pass_devs)
        if scheme is None or dryrun is True:
            return
        active_standard = self.active_grading_standard_id()
        curr_scheme = self.current_grading_standard()
        today = datetime.date.today()
        title = 'Curved Grading {}-{:02}-{:02}'.format(today.year,today.month,today.day)
        arglist = [('title',title)] + scheme
        # send grading scheme to Canvas
        resp = self.post('courses/{}/grading_standards'.format(self.id),arglist)
        if len(resp) > 0:
            resp = resp[0]
        if 'id' not in resp:
            if not self.dryrun:
                print('Unrecognized response from Canvas:\n',resp)
            return
        ## we'de like to make the new scheme the active scheme, but that doesn't seem to be enabled in the API
        if False:
            gs_id = resp['id']
            arglist = [('grading_standard_id',gs_id)]
            resp = self.put('courses/{}/settings'.format(self.id),arglist)
            print(resp)
        return

    def zero_missing_assignment(self, comment = None):
        '''
        Set grades to zero for all students missing an assignment, with an appropriate comment
        '''
        if comment is None:
            comment = "Missed assignment"
        ungraded = self.fetch_ungraded()
        missed = {}
        for uid in ungraded:
            missed[uid] = Grade(0,comment)
        if self.dryrun:
            print("**** IMPORTANT NOTE: the below list indicates who would be marked missing ****")
            print("****   based on what scores were in the gradebook prior to this command!  ****")
        try:
            self.batch_upload_grades(missed)
        except CanvasException as err:
            print(err)
        return

    @staticmethod
    def day_of_year(normdate):
        '''
        extract the day number within a year (1-366) from the normalized YYYYMMDD date integer
        '''
        if type(normdate) is not int or normdate < 20170101 or normdate > 20991231:
            return 0
        month = (normdate // 100) % 100
        day = normdate % 100
        year = normdate // 10000
        month_lengths = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
        daynum = sum(month_lengths[0:month]) + day
        if (year % 4 and year % 100 != 0) and month > 2:
            daynum += 1  # account for leap day
        return daynum
    
    @staticmethod
    def normalize_date(date):
        '''
        convert string YYYY-M-D or YYYY/M/DD into integer YYYYMMDD
        '''
        if date is None:
            dt = datetime.date.today()
            return '{}{:02}{:02}'.format(dt.year,dt.month,dt.day)
        parts = re.split('[-/.]',date)
        return int('{}{:02}{:02}'.format(int(parts[0]),int(parts[1]),int(parts[2])))

    @staticmethod
    def print_course(courseinfo):
        c_id = courseinfo['id']
        name = courseinfo['name'] if 'name' in courseinfo else '{none}'
        if 'concluded' in courseinfo and courseinfo['concluded']:
            name += '  (concluded)'
        created = courseinfo['created_at'] if 'created_at' in courseinfo else 'unspecified'
        start = courseinfo['start_at'] if 'start_at' in courseinfo else 'unspecified'
        code = courseinfo['course_code'] if 'course_code' in courseinfo else 'xx-xxx'
        def_view = courseinfo['default_view'] if 'default_view' in courseinfo else 'unspecified'
        public = courseinfo['is_public'] if 'is_public' in courseinfo else 'No'
        blueprint = courseinfo['blueprint'] if 'blueprint' in courseinfo else 'No'
        enrollment = courseinfo['enrollments'] if 'enrollments' in courseinfo else 'None'
        enrollment = ' '.join([e['type']+'/'+e['enrollment_state'] for e in enrollment])
        num_students = courseinfo['total_students'] if 'total_students' in courseinfo else 0
        print('{} {}'.format(code,name))
        print('   id: {}, default view: {}, public: {}, blueprint: {}'.format(c_id,def_view,public,blueprint))
        print('   created: {}, starts: {}'.format(created,start))
        print('   {} students, role: {}'.format(num_students,enrollment))
        return

    @staticmethod
    def display_assignments(args, search = None):
        course = Course(args.host, args.course, verbose=args.verbose)
        assignments = course.fetch_assignments(search)
        print(assignments)
        return True

    @staticmethod
    def display_courses(args):
        course = Course(args.host, None, verbose=args.verbose)
        courses = course.fetch_courses(student_count=True,concluded=True)
        if not courses:
            print('No courses found')
            return True
        for c in courses:
            Course.print_course(c)
        return True

    @staticmethod
    def display_course_settings(args):
        course = Course(args.host, args.course, verbose=args.verbose)
        settings = course.get('courses/{}/settings'.format(course.id))
        if type(settings) is type([]):
            settings = settings[0]
        for s in settings:
            print('{}: {}'.format(s,settings[s]))
        return True

    @staticmethod
    def display_get(args, endpoint, arglist=[]):
        if len(arglist) % 2 != 0:
            print('must have matched parameter/value pairs')
            return
        course = Course(args.host, args.course)
        params = list(zip(arglist[0::2],arglist[1::2]))
        results = course.get(endpoint,params,True)
        print(results)
        return True

    @staticmethod
    def display_grade_stats(args):
        course = Course(args.host, args.course,verbose=args.verbose)
        grades = course.fetch_running_grades()
        grades.sort()
        if len(grades) > 0:
            print('Min: {}'.format(grades[0]))
            print('Max: {}'.format(grades[-1]))
            if len(grades)%2 == 1:
                print('Median: {}'.format(grades[len(grades)//2]))
            else:
                print('Median: {}'.format((grades[len(grades)//2]+grades[len(grades)//2+1])/2))
            print('Mean: {}'.format(sum(grades) / len(grades)))
            print('StdDev: {}'.format(pstdev(grades)))
        return True

    @staticmethod
    def display_graded(args, assignment):
        course = Course(args.host, args.course, verbose=args.verbose)
        course.find_assignment(assignment)
        graded = course.fetch_graded()
        emails = [email for (uid,email) in graded.items()]
        emails.sort()
        print(len(emails),emails)
        return True

    @staticmethod
    def display_grades(args, assignment):
        course = Course(args.host, args.course, verbose=args.verbose)
        course.find_assignment(assignment)
        ## FIXME
        print("Not yet implemented")
        return True

    @staticmethod
    def display_grading_standards(args):
        course = Course(args.host, args.course, verbose=args.verbose)
        standards = course.fetch_grading_standards()
        active_standard = course.active_grading_standard_id()
        for standard in standards:
            name = standard['title']
            scheme = standard['grading_scheme']
            if name and scheme:
                active_flag = '  '
                if int(standard['id']) == active_standard:
                    active_flag = '* '
                print('{}{}'.format(active_flag,name))
                top = 100
                for grade in scheme:
                    print('    {}  {} to {}%'.format(grade['name'],grade['value']*100.0,top))
                    top = grade['value'] * 100.0
        return True

    @staticmethod
    def display_my_name(args):
        course = Course(args.host, args.course)
        print(course.whoami())
        return True

    @staticmethod
    def display_delete(args, endpoint, arglist=[]):
        if len(arglist) % 2 != 0:
            print('must have matched parameter/value pairs')
            return True
        course = Course(args.host, args.course)
        course.simulate(args.dryrun)
        params = list(zip(arglist[0::2],arglist[1::2]))
        results = course.delete(endpoint,params)
        print(results)
        return True

    @staticmethod
    def display_post(args, endpoint, arglist=[]):
        if len(arglist) % 2 != 0:
            print('must have matched parameter/value pairs')
            return True
        course = Course(args.host, args.course)
        course.simulate(args.dryrun)
        params = list(zip(arglist[0::2],arglist[1::2]))
        results = course.post(endpoint,params)
        print(results)
        return True

    @staticmethod
    def display_put(args, endpoint, arglist=[]):
        if len(arglist) % 2 != 0:
            print('must have matched parameter/value pairs')
            return True
        course = Course(args.host, args.course)
        course.simulate(args.dryrun)
        params = list(zip(arglist[0::2],arglist[1::2]))
        results = course.put(endpoint,params)
        print(results)
        return True

    @staticmethod
    def display_reviews(args, assignment):
        if assignment is None:
            print('You must specify an assignment name with -a')
            return True
        course = Course(args.host, args.course, verbose=args.verbose)
        course.find_assignment(assignment)
        if course.assignment_id is None:
            return True
        reviews = course.fetch_reviews()
        if type(reviews) is not list:
            reviews = [reviews]
        for review in reviews:
            user = review['user']
            reviewer = review['assessor']
            status = review['workflow_state']
            print('review of',user['display_name'],'by',reviewer['display_name'],'is',status)
            if status == 'completed':
                print('  comments:',review['submission_comments'])
        return True

    @staticmethod
    def display_roster(args):
        course = Course(args.host, args.course, verbose=args.verbose)
        if args.liststudents:
            header = 'UserID,Name,Email'
        else:
            header = 'Email,Name'
        print(header)
        for student in course.fetch_roster():
            uid = str(student['id'])
            email = student['login_id']
            name = student['name']
            if args.liststudents:
                print(','.join([uid,name,email]))
            else:
                print(email + ',' + name)
        if args.verbose:
            print('********* DROPPED ***********')
            print(header)
            for student in course.fetch_drops():
                uid = str(student['id'])
                email = student['login_id']
                name = student['name']
                if args.liststudents:
                    print(','.join([uid,name,email]))
                else:
                    print(email + ',' + name)
        return True

    @staticmethod
    def display_rubric_ids(host, course_name, verbose = False):
        course = Course(host, course_name, verbose=verbose)
        rubrics = course.fetch_rubrics()
        print(rubrics)
        return

    @staticmethod
    def display_rubric(host, course_name, id, verbose = False):
        course = Course(host, course_name,verbose=verbose)
        rubric = course.fetch_rubric(id, which='peer_assessments')
        print(rubric)
        return

    @staticmethod
    def display_rubric_def(args, assignment):
        course = Course(args.host, args.course, verbose=args.verbose)
        course.find_assignment(assignment)
        if course.assignment_id is None:
            return True
        rubric = course.fetch_rubric_def()
        if rubric:
            rubric.display()
        else:
            print('Assignment',assignment,'has no rubric')
        return True

    @staticmethod
    def display_todo(args):
        course = Course(args.host, args.course, verbose=args.verbose)
        todo = course.fetch_todo()
        for item in todo:
            action = item['type']
            due = 'Undated'
            name = 'untitled'
            assignment = item['assignment']
            to_grade = ''
            if 'name' in assignment:
                name = assignment['name']
            if 'due_at' in assignment:
                due = assignment['due_at']
            if 'needs_grading_count' in item and \
                   type(item['needs_grading_count']) is int and \
                   item['needs_grading_count'] > 0:
                to_grade = '({})'.format(item['needs_grading_count'])
            print('{}: {} {} {}'.format(due,action,name,to_grade))
        return True

    @staticmethod
    def display_ungraded(args, assignment):
        course = Course(args.host, args.course, verbose=args.verbose)
        course.find_assignment(assignment)
        ungraded = course.fetch_ungraded()
        emails = [email for (uid,email) in ungraded.items()]
        emails.sort()
        if len(emails) > 0:
            print(len(emails),emails)
        else:
            print("No ungraded items found")
        return True

    @staticmethod
    def display_upcoming(args):
        course = Course(args.host, args.course, verbose=args.verbose)
        upcoming = course.fetch_upcoming()
        for item in upcoming:
            title = item['title']
            date = 'Undated'
            if 'all_day_date' in item:
                date = item['all_day_date']
            if date is None and 'end_at' in item:
                date = item['end_at'][:10]
            print('{}: {}'.format(date,title))
        return True

    @staticmethod
    def process_generic_commands(args, remargs):
        if args.get is True:
            return Course.display_get(args, remargs[0],remargs[1:])
        if args.graded is True:
            return Course.display_graded(args, args.assignment)
        if args.gradestats is True:
            return Course.display_grade_stats(args)
        if args.listassignments is True:
            return Course.display_assignments(args, args.assignment)
        if args.listcourses is True:
            return Course.display_courses(args)
        if args.listcurves is True:
            return Course.display_grading_standards(args)
        if args.listgrades is True:
            return Course.display_grades(args.host, args.course, args.assignment,args.verbose)
        if args.listreviews is True:
            return Course.display_reviews(args, args.assignment)
        if args.settings is True:
            return Course.display_course_settings(args)
        if args.post is True:
            return Course.display_post(args, remargs[0], remargs[1:])
        if args.put is True:
            return Course.display_put(args, remargs[0], remargs[1:])
        if args.roster is True or args.liststudents is True:
            return Course.display_roster(args)
        if args.showrubric is True:
            return Course.display_rubric_def(args, args.assignment)
        if args.todo is True:
            return Course.display_todo(args)
        if args.ungraded is True:
            return Course.display_ungraded(args, args.assignment)
        if args.upcoming is True:
            return Course.display_upcoming(args)
        if args.whoami is True:
            return Course.display_my_name(args)
        if args.zeromissing is True:
            course = Course(args.host, args.course)
            course.simulate(args.dryrun)
            course.find_assignment(args.assignment)
            if course.assignment_id is not None:
                course.zero_missing_assignment()
            return True
        if args.delete is True:
            return Course.display_delete(args, remargs[0], remargs[1:])
        return False

    def parse_arguments(host, course_name, flag_adder = None):
        parser = argparse.ArgumentParser(description="Commandline control of Canvas gradebook")
        parser.add_argument("-n","--dryrun",action="store_true",help="do everything except actually change values on server")
        parser.add_argument("-a","--assignment",metavar="NAME",help="the name of the assignment being graded")
        parser.add_argument("-p","--points",metavar="POINTS",help="points possible for the assignment")
        parser.add_argument("-d","--dir",metavar="DIR",default=".",help="directory in which to store files submitted for assignment")
        parser.add_argument("-v","--verbose",action="store_true",help="run with verbose output")
        parser.add_argument("-t","--due",metavar="DATE",help="the assignment was due at YYYY-MM-DD (NYI)")
        parser.add_argument("-R","--roster",action="store_true",help="only download and display the roster")
        parser.add_argument("-g","--grade",metavar="GRADE",default=None,help="the grade to assign when updating a single student")
        parser.add_argument("-m","--message",metavar="MSG",default=None,help="the feedback to give the student")
        parser.add_argument("-s","--student",metavar="ID",help="the Andrew ID of the student whose grade is to be updated")
        parser.add_argument("-u","--uid",metavar="UID",help="the student's SIS ID number")
        parser.add_argument("--graded",action="store_true",help="display list of studentIDs for which there is a grade in the assignment")
        parser.add_argument("--gradestats",action="store_true",help="show class average grades")
        parser.add_argument("--listassignments",action="store_true",help="display list of assignments for course")
        parser.add_argument("--listcurves",action="store_true",help="show available grading standards for course")
        parser.add_argument("--listgrades",action="store_true",help="show student grades for the specified assignment (NYI)")
        parser.add_argument("--listrubrics",action="store_true",help="display list of IDs for active rubrics")
        parser.add_argument("--listreviews",action="store_true",help="display list of peer reviews for the assignment")
        parser.add_argument("--liststudents",action="store_true",help="display list of students by email and Canvas userID")
        parser.add_argument("--showrubric",action="store_true",help="show the rubric definition for the assignment")
        parser.add_argument("--listcourses",action="store_true",help="list all of your courses")
        parser.add_argument("--settings",action="store_true",help="display course settings")
        parser.add_argument("--todo",action="store_true",help="retrieve personal TODO list")
        parser.add_argument("--ungraded",action="store_true",help="display list of studentIDs for which there is no grade in the assignment")
        parser.add_argument("--upcoming",action="store_true",help="display list of upcoming calendar events")
        parser.add_argument("--whoami",action="store_true",help="show the name under which I am authenticated")
        parser.add_argument("--zeromissing",action="store_true",help="assign zero scores for missing assignments to all ungraded students")
        if flag_adder:
            if type(flag_adder) is type([]):
                for adder in flag_adder:
                    adder(parser)
            else:
                flag_adder(parser)
        parser.add_argument("--host",metavar="HOST",default=host,help="set host name of Canvas server")
        parser.add_argument("--course",metavar="NAME",default=course_name,help="name of the course")
        parser.add_argument("--get",action="store_true",help="perform a raw API 'get' call")
        parser.add_argument("--put",action="store_true",help="perform a raw API 'put' call (USE CAUTION!)")
        parser.add_argument("--post",action="store_true",help="perform a raw API 'post' call (USE CAUTION!)")
        parser.add_argument("--delete",action="store_true",help="perform a raw API 'delete' call (USE CAUTION!)")
        if len(sys.argv) <= 1:
            parser.print_usage()
            parser.exit()
        args, remargs = parser.parse_known_args()
        if args.due is not None:
            args.due = Course.normalize_date(args.due)
            args.due_day = Course.day_of_year(args.due)
        else:
            args.due_day = 999
        return args, remargs

######################################################################

class CanvasCSV():
    def __init__(self, file):
        self.csv = csv.reader(file)
        self.eof = False
        self.row = None
        return
    
    def next_row(self):
        '''
        Get the next row of the .csv file represented by the CSVReader
        '''
        try:
            self.row = self.csv.__next__()
        except StopIteration:
            self.row = None
            self.eof = True
        return self.row
    
    def get_index(self, field):
        '''
        Locate a column in the .csv file by checking the first line of the file
        '''
        try:
            idx = self.row.index(field)
        except:
            idx = -1
        return idx

    def get_field(self, index):
        '''
        Retrieve a field out of the given row of a .csv file
        '''
        if index < 0:
            return None
        value = self.row[index]
        if '.00' in value:
            try:
                v = float(value)
                value = int(v)
            except:
                pass
        return value

    @staticmethod
    def convert_to_csv(filelist,tmpdir):
        '''
        Use OpenOffice/LibreOffice to convert a list of spreadsheet files to CSV format
        '''
        if filelist == []:
            return filelist
        homedir = os.environ['HOME']
        ## BUG: LibreOffice prior to v5.3 (July 2016) silently fails if
        ##  another instance is already running, so we need to specify an
        ##  alternate config directory dedicated to the conversion
        soffice = ['soffice','--convert-to','csv',
                   '-env:UserInstallation=file://{}/.LibreOffice_Headless'.format(homedir),
                   '--headless','--outdir',tmpdir]
        try:
            check_output(soffice + filelist,shell=False)
        except CalledProcessError as err:
            print(err.cmd,'returned exit code',err.returncode,'and generated the following output:')
            print(err.output)
            return []
        except Exception as err:
            print(err)
            return []
        return [fn.rsplit('.',1)[0]+'.csv' for fn in filelist]

    @staticmethod
    def sanitize_csv(filename):
        '''
        Remove non-ASCII characters from a CSV file using 'iconv'
        '''
        inp = filename
        out = filename + '.txt'
        with open(inp,'r') as infile:
            with open(out,'w') as outfile:
                exitcode = call(['iconv','-f','utf-8','-t','ascii','-c'], stdin=infile, stdout=outfile)
        if exitcode != 0:
            with open(inp,'r') as infile:
                with open(out,'w') as outfile:
                    exitcode = call(['iconv','-f','windows-1251','-t','ascii/translit//ignore','-c'],
                                     stdin=infile,stdout=outfile)
        if exitcode == 0:
            call(['mv',out,inp])
        return

    @staticmethod
    def convert_files_to_csv(filelist,tmpdir):
        '''
        Convert a list of spreadsheet files to CSV format if they are not already a .csv, and sanitize
        all of the files.  Returns a list of filenames of the resulting .csv files
        '''
        noncsv = [fn for fn in filelist if fn[-4:] != '.csv']
        csv = CanvasCSV.convert_to_csv(noncsv,tmpdir)
        csv += [fn for fn in filelist if fn[-4:] == '.csv']
        # iterate over all the CSV files in the directory (both those that were originally there
        #   and those we created as conversions from other formats) and apply some sanitization
        for filename in csv:
            CanvasCSV.sanitize_csv(filename)
        return csv

######################################################################

if __name__ == '__main__':
    print('This module is not intended to be run standalone.')

### end of file canvaslms.py ###
