#!/bin/env python3

##  by Ralf Brown, Carnegie Mellon University
##  last edit: 13feb2018

import csv
import math
import os
import random
import re
import sys
import urllib, urllib.request
from urllib.error import HTTPError
from statistics import mean  # requires Python 3.4+

from canvaslms import Course, Grade, CanvasCSV

######################################################################

## configuration
COURSE_NAME = "Coding & Algorithms Bootcamp"
HOST = "canvas.cmu.edu"
MAIL = "@andrew.cmu.edu"
TEST_STUDENT = 10839 # uid of the Test Student for the course
## People whose comments should be ignored when processing peer reviews.  Use the display_name for each.
COURSE_STAFF = ['Ralf Brown']

## for very skewed grades, we may want to compute standard deviation separately for grades above and below the mean
SPLIT_STDDEV = True

## configuration of late penalty: percent per day and maximum days late accepted
LATE_PERCENT = 10
LATE_DAYS = 7

######################################################################

def add_bootcamp_flags(parser):
    '''
    add the flags specific to 11-601 to the given argument parser
    '''
    parser.add_argument("-I","--inclass",action="store_true",help="interpret CSV file as an in-class exercise")
    parser.add_argument("-H","--homework",action="store_true",help="interpret CSV file as a homework assignment")
    parser.add_argument("-S","--shuffle",metavar="NAME",help="use assignment NAME as source of grades for shuffle assessment")
    parser.add_argument("-F","--feedback",metavar="NAME",help="use assignment NAME as source of grades for shuffle feedback")
    parser.add_argument("--makecurve",action="store_true",help="compute curve for mean of 85%% and stdev of 5%%")
    parser.add_argument("--makeshuffle",action="store_true",help="create interview shuffle among the enrolled students")
    parser.add_argument("--reassign",action="store_true",help="assign a new interviewee to an interviewer")
    parser.add_argument("-Q","--questions",metavar="FILE",help="load list of shuffle questions from FILE")
    parser.add_argument("--students",metavar="FILE",help="use list of students in FILE instead of current roster for --makeshuffle")
    parser.add_argument("--addreviewer")
    parser.add_argument("--old",action="store_true",help="use .csv files for shuffle scores instead of rubric")
    return

######################################################################

def build_feedback(partnum, total, mcq, coding, subscores):
    subscores = [x for x in subscores if 'Not Applicable' not in str(x)]
    comment = 'Part {}: '.format(partnum+1) if partnum >= 0 else ''
    if mcq is None:
        comment += '{} points'.format(int(total))
    else:
        comment += '{}mcq+{}code'.format(Grade.drop_decimals(mcq),Grade.drop_decimals(coding))
    if sum(1 for x in subscores if x is not None) > 1:
        subs = (Grade.drop_decimals(x) if x is not None else '-' for x in subscores)
        comment += '; per-Q: ' + ':'.join(subs)
    return comment
    
######################################################################

def parse_hackerrank(course, csv, grades, partnum, verbose=False):
    ## extract the column numbers of interest from the first row
    row = csv.next_row()
    idx_date = csv.get_index('Date taken')
    idx_email = csv.get_index('Login ID')
    idx_andrew = csv.get_index('Andrew')
    if idx_andrew == -1:
        idx_andrew = csv.get_index('AndrewID')
    if idx_andrew == -1:
        idx_andrew = csv.get_index('Andrew ID')
    idx_mcq = csv.get_index('MCQ')
    idx_coding = csv.get_index('Coding')
    idx_score = csv.get_index('Total score')
    idx_date = csv.get_index('Date taken')  # was the assignment late?
    idx_qs = [csv.get_index('Question '+str(num)) for num in range(1,100)]
    while not csv.eof:
        row = csv.next_row()
        if not row:
            break
        submit_date = csv.get_field(idx_date)
        email = csv.get_field(idx_email)
        andrew = csv.get_field(idx_andrew)
        mcq = csv.get_field(idx_mcq)
        coding = csv.get_field(idx_coding)
        total = csv.get_field(idx_score)
        subscores = [csv.get_field(i) for i in idx_qs if i >= 0]
        uid = course.get_student_id(email,andrew)
        if uid is None:
            continue	# non-existent or dropped student
        comment = build_feedback(partnum,total,mcq,coding,subscores)
        if uid in grades:
            gr = grades[uid]
        else:
            gr = Grade()
            grades[uid] = gr
        if verbose:
            print('   adding',uid,partnum,email,total,comment)
        if total is not None:
            pn = partnum if partnum >= 0 else 0
            gr.add(total,comment,pn,course.late_penalty(submit_date))
    return

######################################################################

def extract_andrew_from_filename(filename,what='feedback'):
    return filename.rsplit('_{}'.format(what),-1)[0]
    
######################################################################

def parse_shuffle_assessment(course,csv,filename,grades,verbose = False):
    # read header line
    row = csv.next_row()
    if "Feedback" in row[0]:
        print('*',extract_andrew_from_filename(filename,'assessment'),"submitted an Interviewer Feedback")
        return
    # skip second header line
    csv.next_row()
    # read AndrewIDs and Q1/Q2/Q3/Overall scores
    row = csv.next_row()
    andrew = email_to_AndrewID(row[1])
    ##FIXME: massage AndrewID
    try:
        totalscore = float(row[14])
    except:
        print('Bad totalscore in',filename)
        totalscore = -1
        had_error = True

    # skip empty line
    csv.next_row()
    # skip header line
    csv.next_row()
    # skip second header line
    csv.next_row()
    q1 = []
    q2 = []
    q3 = []
    had_error = False
    for i in range(7):
        # get rubric score i for the three questions
        row = csv.next_row()
        if row is None:
            print('Bad data in',filename)
            had_error = True
            q1 += ['?']
            q2 += ['?']
            q3 += ['?']
        else:
            q1 += [row[0]]
            q2 += [row[1]]
            q3 += [row[2]]
    # skip empty line
    csv.next_row()
    # skip header line
    csv.next_row()
    # skip second header line
    csv.next_row()
    overall = []
    for i in range(5):
        row = csv.next_row()
        if row is None:
            had_error = True
        else:
            overall += [row[0]]
    # skip empty line
    csv.next_row()
    # skip header line
    csv.next_row()
    # read feedback text
    row = csv.next_row()
    if row is None:
        had_error = True
        feedback = ''
    else:
        feedback = row[3]
    try:
        # strip decimal part of total score
        base_score = int(totalscore)
    except:
        base_score = 0
    if base_score == 0:
        print('-',filename,'gives zero score')
    # validity checks
    if andrew is None or andrew == '':
        print('*',filename,"does not include interviewee's Andrew ID")
        return
    uid = course.get_id_for_student(andrew)
    if uid is None:
        print('*',filename,'contains an unknown Andrew ID:',andrew)
        return
    if uid in grades:
        print('=',filename,"contains an Andrew ID we've already seen:",andrew)
        return
    # reformat the information into a comment for the gradebook
    comment = 'Q1: {}/{}/{}/{}/{}/{}/{}'.format(q1[0],q1[1],q1[2],q1[3],q1[4],q1[5],q1[6])
    if ''.join(q2) != '':
        comment += '\nQ2: {}/{}/{}/{}/{}/{}/{}'.format(q2[0],q2[1],q2[2],q2[3],q2[4],q2[5],q2[6])
    if ''.join(q3) != '':
        comment += '\nQ3: {}/{}/{}/{}/{}/{}/{}'.format(q3[0],q3[1],q3[2],q3[3],q3[4],q3[5],q3[6])
    comment += '\nOverall: {}/{}/{}/{}/{}'.format(overall[0],overall[1],overall[2],overall[3],overall[4])
    comment += '\nFeedback: {}'.format(feedback)
    ## insert score and comment into 'grades'
    if had_error:
        print('Bad data in',filename,', best guess is:')
        print(' ',andrew,totalscore,comment)
    if verbose:
        print("  adding",uid,andrew,totalscore,comment)
    grades[uid] = Grade(totalscore,comment)
    return

######################################################################

def email_to_AndrewID(login):
    if MAIL in login:
        login, m, rest = login.rpartition(MAIL)
    return login.strip().lower()

######################################################################

def parse_shuffle_feedback(course, csv, filename, grades, verbose = False):
    if '_feedback' in filename:
        user = filename.rsplit('_feedback',-1)[0]
    else:
        user = None
    ## extract the column numbers of interest from the first row
    row = csv.next_row()
    if "Interviewee:" in row or "Location" in row[3]:
        print('*',extract_andrew_from_filename(filename),"submitted an Interviewee Assessment")
        return
    # skip the second row, which contains user instructions
    row = csv.next_row()
    if 'Andrew' in row:
        # file format error?  Possibly shifted contents of spreadsheet
        print(filename,"is an unrecognized file")
        return
    # third row contains interviewer's AndrewID and overall criterion scores + final average
    row = csv.next_row()
    andrew = row[0]
    # massage Andrew ID
    andrew = email_to_AndrewID(andrew)
    overall_score = row[14]
    # skip empty row
    csv.next_row()
    # skip header line
    csv.next_row()
    crit = [0]*4
    for i in range(4):
        row = csv.next_row()
        if row[0] == '':
            print('!',filename,' contains blank entry in rubric')
            crit[i] = 0
        else:
            try:
                crit[i] = float(row[0])
            except:
                print('*',filename,' contains invalid entry in rubric')
                return
    # skip next header line
    csv.next_row()
    # read comments line
    row = csv.next_row()
    comment = '(no comment given)' if row is None else ''.join(row) 
    ## validity checks
    if andrew is None or andrew == "":
        print('*',filename," does not contain an Interviewer ID")
        return
    if andrew == user:
        print("= user",andrew,"entered own ID as interviewer")
        return
    uid = course.get_id_for_student(andrew)
    if uid is None:
        print('*',filename,"contains an unknown Andrew ID:",andrew)
        return
    if uid in grades:
        print('+',filename,"contains an Andrew ID we've already seen:",andrew)
        return
    ## OK, we've got a good feedback form, so massage the data
    ## we're changing the score in Canvas to be 0-12 to be compatible with an upcoming switch to rubric scoring,
    ##   so just add up the subscores
    overall_score = sum(crit)
    feedback = 'Subscores: {}/{}/{}/{}, Feedback: {}'.format(crit[0],crit[1],crit[2],crit[3],comment)
    if verbose:
        print("  adding",uid,andrew,overall_score,feedback)
    grades[uid] = Grade(overall_score,feedback)
    return

######################################################################

def process_grades(course, flags, csv_files):
    grades = {}
    for (i, csv_file) in enumerate(csv_files):
        with open(csv_file,"r") as f:
            csvfile = CanvasCSV(f)
            if flags.inclass:
                print('processing',csv_file)
                parse_hackerrank(course,csvfile,grades,-1,flags.verbose)
            elif flags.homework:
                print('processing',csv_file)
                parse_hackerrank(course,csvfile,grades,i,flags.verbose)
            elif flags.shuffle:
                parse_shuffle_assessment(course,csvfile,csv_file,grades,flags.verbose)
            elif flags.feedback:
                parse_shuffle_feedback(course,csvfile,csv_file,grades,flags.verbose)
    if flags.inclass or flags.homework:
        numparts = len(csv_files)
    else:
        numparts = 1
    course.batch_upload_grades(grades,numparts)
    if flags.inclass:
        course.zero_missing_assignment()
    return

######################################################################

def process_shuffle_assessment(submissions, rubric_def, rubric_grades, submit_grades, assessors,
                               submit_points, course, verbose = False):
    if verbose:
        print(len(submissions),'total submissions retrieved')
    for sub in submissions:
        if sub['id'] not in assessors:
            continue
        pts = submit_points
        remarks = ''
        attachments = []
        if 'submission_comments' in sub:
            for com in sub['submission_comments']:
                if 'attachments' in com and com['attachments'] and com['author']['display_name'] not in COURSE_STAFF:
                    for a in com['attachments']:
                        ctype = 'unknown'
                        if 'content-type' in a:
                            ctype = a['content-type']
                        attachments += (a['filename'],ctype,a['mime_class'],a['url'])
        if verbose:
            print('Attachments:',attachments)
        uid = sub['user_id']
        reviewer, _, criteria = assessors[sub['id']]
        crit_points = {}
        for crit in criteria:
            if 'points' not in crit or 'criterion_id' not in crit or crit['points'] < 0.0:
                continue		# N/A or non-scored criterion
            points = crit['points']
            c_id = crit['criterion_id']
            name = rubric_def.get_name(c_id)
            if not name:
                continue
            if name[0] == 'Q' and name[2] == ':':
                name = name[4:]
            if 'Suggestions' in name:
                if len(crit['comments']) < 8:
                    pts = pts - (0.05 * submit_points)
                    remarks += 'Did not provide suggested improvements (-{})\n'.format(Grade.drop_decimals(0.05*submit_points))
                continue
            if 'Location' in name:
                if len(crit['comments']) < 8:
                    pts = pts - (0.05 * submit_points)
                    remarks += 'Did not specify location/time (-{})\n'.format(Grade.drop_decimals(0.05*submit_points))
                continue
            if name in crit_points:
                crit_points[name] = crit_points[name] + [points]
            else:
                crit_points[name] = [points]
        total_points = 0
        possible = 0
        if verbose:
            print('crit_points:',crit_points)
        for itemname, pointlist in crit_points.items():
            total_points += mean(pointlist)
            possible += 3
        if total_points == 0:
            print('!  {} ({}) received a zero score'.format(course.student_login(uid),uid))
        if possible > 0:
            grade = 12.0 * (total_points / possible)
            rubric_grades[uid] = 12.0 * (total_points / possible)
        else:
            grade = None
            print('empty rubric for {} ({})'.format(course.student_login(uid),uid))
        if reviewer is not None:
            if attachments == []: ##FIXME
                pts = pts - (0.30 * submit_points)
                remarks += 'Did not upload photo (-{})'.format(Grade.drop_decimals(0.30*submit_points))
            submit_grades[reviewer] = Grade(pts,remarks)
            if verbose or True: ##DEBUG
                print(' ',course.student_login(reviewer),'entered',grade,'for',course.student_login(uid))
    return

######################################################################

def process_shuffle_rubric(course, flags):
    if flags.feedback:
        submit_assign_id = course.find_assignment_id(flags.feedback)
        return course.confirm_peer_review_scores(course.assignment_id,submit_assign_id)
    submit_assign_id = course.find_assignment_id(flags.shuffle)
    return course.confirm_peer_review_scores(course.assignment_id,submit_assign_id,process_shuffle_assessment)

######################################################################

def process_shuffle_csv(course, flags):
    if flags.feedback:
        what = 'feedback'
        submit_assign = flags.feedback
    else:
        what = 'assessment'
        submit_assign = flags.shuffle
    submit_assign_id = course.find_assignment_id(submit_assign)
    if submit_assign_id is None:
        return
    # get both current and former students, since someone may have uploaded feedback before dropping the course
    submissions = course.fetch_assignment_submissions(submit_assign_id)
    spreadsheets = []
    submit_grades = {}
    for sub in submissions:
        if sub['workflow_state'] != 'submitted':
            continue
        uid = sub['user_id']
        late_seconds = sub['seconds_late']
        late_days = (late_seconds + 86100) // 86400
        login = course.student_login(uid)
        attachments = sub['attachments']
        spreadsheet_url = None
        upload_filename = None
        filename = None
        suffix = None
        for attach in attachments:
            if 'filename' not in attach or 'content-type' not in attach or 'url' not in attach:
                continue
            mimetype = attach['content-type']
            if 'spreadsheet' in mimetype:
                spreadsheet_url = attach['url']
                filename = attach['filename']
                (base, period, suffix) = filename.rpartition('.')
        if spreadsheet_url:
            destfile = '{}/{}_{}.{}'.format(flags.dir,login,what,suffix)
            print('Downloading',what,'by',login)
            try:
                urllib.request.urlretrieve(spreadsheet_url,filename=destfile)
            except Exception as err:
                print(err)
            else:
                spreadsheets += [destfile]
                if flags.verbose:
                    print(spreadsheet_url,'->',destfile)
            uid = course.get_id_for_student(login)
            if uid is not None and uid > 0:
                gr = Grade()
                gr.add(10,'',0,course.late_penalty_by_days(late_days))
                submit_grades[uid] = gr
        else:
            print('-',login,'did not upload',what,'spreadsheet')
    print('')
    print('Uploading grades for submitting',what)
    course.batch_upload_grades(submit_grades,1,submit_assign_id)
    print('')
    csv_files = CanvasCSV.convert_files_to_csv(spreadsheets,flags.dir)
    process_grades(course,flags,csv_files)
    return

######################################################################

def autodetect(flags,filename):
    with open(filename,'r') as f:
        pass
    ## FIXME
    return False

######################################################################

def make_interview(interviewers, i, questions):
    if i+1 < len(interviewers):
        interviewee = interviewers[i+1]
    else:
        interviewee = interviewers[0]
    if i > 0:
        rev_interviewer = interviewers[i-1]
    else:
        rev_interviewer = interviewers[len(interviewers)-1]
    for it in range(32):
        random.shuffle(questions)
        # extract the chapter numbers of the first three shuffled questions
        f3chap = list(map(lambda x: int(x.split('.')[0]), questions[:3]))
        # try to get questions from three different chapters
        if it < 24 and (f3chap[0] == f3chap[1] or f3chap[1] == f3chap[2] or f3chap[0] == f3chap[2]):
            continue # try again
        # after the 24th try, we'll accept anything except all three questions from the same chapter
        if sum(f3chap) != (3 * f3chap[0]):
            break
    return [interviewee,rev_interviewer] + questions[:3]

######################################################################

def assign_interviews(interviewers, questions):
    # split() generates empty element when file ends with a newline, so strip off those empty elements
    #   from the interviewers and questions lists if present
    num_i = len(interviewers)
    if num_i > 0 and interviewers[num_i-1] == '':
        interviewers = interviewers[0:num_i-1]
    num_q = len(questions)
    if num_q > 0 and questions[num_q-1] == '':
        questions = questions[0:num_q-1]

    random.shuffle(interviewers)
    interviews = {}
    i = 0
    for interviewer in interviewers:
        interviews[interviewer] = make_interview(interviewers,i,questions)
        i = i+1
    return interviews
    
######################################################################

def make_shuffle(course,flags):
    if not flags.feedback:
        print('You must specify the feedback assignment with --feedback')
        return
    feedback_assign_id = course.find_assignment_id(flags.feedback)
    if feedback_assign_id is None:
        print('The requested feedback assignment was not found')
        return
    questions = flags.questions
    if questions is None:
        questions = 'problems.txt'
    with open(questions) as f:
        q = f.read().split('\n')
    students = flags.students
    if students is None:
        student_ids = course.fetch_active_students()
        interviewers = [email_to_AndrewID(login) for login in student_ids]
    else:
        if students == '.' or students == '=':
            students = 'students.txt'
        with open(students) as f:
            interviewers = f.read().split('\n')

    interviews = assign_interviews(interviewers,q)

    # create output directory
    directory = flags.dir
    if directory is None or directory == '' or directory == '.':
        directory = 'shuffle'
    if not os.path.exists(directory):
        os.makedirs(directory)

    log = open('assignments.log','a')
    log.write('Shuffle assignments for {}/{}\n'.format(flags.assignment,flags.feedback))

    assessment_reviews = {}  # map from student to their interviewer, who will leave a peer review for them
    feedback_reviews = {}  # map from student to their interviewee, who will leave a peer review for them
    grades = {}
    feedback_links = {}
    for (interviewer, iview) in interviews.items():
        log.write('{} -> {}  Q1: {}  Q2: {}  Q3: {}\n'.format(interviewer,iview[0],iview[2],iview[3],iview[4]))
        if flags.verbose:
            print(interviewer,'->',iview[0],' Q1:',iview[2],' Q2:',iview[3],' Q3:',iview[4])
        interviewee = iview[0]
        rev_interviewer = iview[1]
        assessment_reviews[interviewee] = interviewer
        feedback_reviews[interviewer] = interviewee
        uid = course.get_id_for_student(interviewer)
        interviewer_uid = course.get_id_for_student(rev_interviewer)
        fb_link = course.peer_review_user_link(feedback_assign_id,interviewer_uid)
        if uid is not None and uid > 0:
            interviewee_uid = course.get_id_for_student(interviewee)
            assess_link = course.peer_review_user_link(course.assignment_id,interviewee_uid)
            grades[uid] = Grade(0,('You will interview: {}\n'+
                                   'The questions to ask: {}  {}  {}\n'+
                                   'You will be interviewed by: {}\n\n'+
                                   'The feedback peer review link is: {}')
                                .format(interviewee,iview[2],iview[3],iview[4],rev_interviewer,fb_link))
#FIXME
#            grades[uid] = Grade(0,('You will interview: {}\n'+
#                                   'The questions to ask: {}  {}  {}\n'+
#                                   'You will be interviewed by: {}\n\n'+
#                                   'The assessment peer review link is: {}')
#                                   'The feedback peer review link is: {}')
#                                .format(interviewee,iview[2],iview[3],iview[4],rev_interviewer,assess_link,fb_link))
        if len(fb_link) > 0:
            feedback_links[uid] = Grade(0,('You will be interviewed by: {}\n'+
                                           'The feedback link is: {}\n')
                                        .format(rev_interviewer,fb_link))
    log.close()

    # upload peer-review assignments to the Canvas assignment named by the -a flag
#FIXME    course.add_peer_reviewers(assessment_reviews,course.assignment_id)
    # upload a comment for each student informing them of their interviewee/questions/interviewer
    course.batch_upload_grades(grades,0)

    # upload peer-review assignments to the Canvas assignment named by the --feedback flag
    course.add_peer_reviewers(feedback_reviews,feedback_assign_id)
    # upload a comment for each student informing them of their interviewer and providing the link to the peer review
    course.batch_upload_grades(feedback_links,0,feedback_assign_id)

    return

######################################################################

def reassign(flags, remargs):
    if flags.shuffle is None or flags.feedback is None:
        print('You must specify both shuffle and feedback assignments with --shuffle and --feedback')
        return
    if not remargs:
        print('No reassignments specified')
        return
    course = Course(HOST, COURSE_NAME, verbose=flags.verbose)
    course.simulate(flags.dryrun)
    course.mail_address(MAIL)
    # get the assignment IDs for the interviewee assessment and interviewer feedback
    assessment_id = course.find_assignment_id(flags.shuffle)
    if assessment_id is None:
        print('Did not find assignment',flags.shuffle,'for shuffle')
        return
    feedback_id = course.find_assignment_id(flags.feedback)
    if feedback_id is None:
        print('Did not find assignment',flags.feedback,'for feedback')
        return
    # retrieve the current peer associations  ##FIXME
#    peer_feedbacks = course.fetch_reviews(feedback_id,True)
#    peer_assessments = course.fetch_reviews(assessment_id,True)
    # process the requested reassignments
    interviewers = {}
    assessment_comments = {}
    feedback_comments = {}
    assessment_reviews = {}
    feedback_reviews = {}
    for pair in remargs:
        interviewer, _, interviewee = pair.partition(':')
        interviewer_uid = course.get_student_id(interviewer)
        if interviewer_uid is None or interviewer_uid < 0:
            print('Interviewer "{}" not found'.format(interviewer))
            continue
        interviewee_uid = course.get_student_id(interviewee)
        if interviewee_uid is None or interviewee_uid < 0:
            print('Interviewee "{}" not found'.format(interviewer))
            continue
        interviewers[interviewer_uid] = interviewer
        # build the link to the peer review page for the interviewer
        fb_link = course.peer_review_user_link(feedback_id,interviewer_uid)
        # store the new assignments
        assessment_reviews[interviewee] = interviewer
        feedback_reviews[interviewer] = interviewee
        # add comments informing the students of the new assignments
        new_interviewer_comment = ('You have been assigned a new interviewer: {}\n'+ \
                                  'The feedback peer review link is: {}\n').format(interviewer,fb_link)
        if interviewee_uid not in assessment_comments:
            assessment_comments[interviewee_uid] = Grade()
        assessment_comments[interviewee_uid].add(0,new_interviewer_comment)
        new_interviewee_comment = 'You have been re-assigned to interview: {}'.format(interviewee)
        if interviewer_uid not in assessment_comments:
            assessment_comments[interviewer_uid] = Grade()
        assessment_comments[interviewer_uid].add(0,new_interviewee_comment)
        feedback_comments[interviewee_uid] = Grade(0,('Your interview has been re-assigned.\n'+ \
                                                   'Your new interviewer is: {}\n'+ \
                                                   'The feedback link is: {}\n').format(interviewer,fb_link))
    if False:
        # remove existing peer-review assignments for interviewees from the Canvas assignment named by
        # the --shuffle flag, then upload the new peer-review assignments
        print("removing peer reviewers in assignment",flags.shuffle)
        course.remove_peer_reviewers(feedback_comments.keys(),assessment_id)
        course.add_peer_reviewers(assessment_reviews,assessment_id)
    # upload a comment for each student informing them of their new interviewee
    course.batch_upload_grades(assessment_comments,0,assessment_id)
    # remove existing peer reviews for interviewer from the Canvas assignment named by the --feedback flag
    # then upload the new peer-review assignments
    print("removing peer reviewers in assignment",flags.feedback)
    course.remove_peer_reviewers(interviewers.keys(),feedback_id)
    course.add_peer_reviewers(feedback_reviews,feedback_id)
    # upload a comment for each student informing them of their new interviewer
    course.batch_upload_grades(feedback_comments,0,feedback_id)

    return

######################################################################

def main():
    args, remargs = Course.parse_arguments(HOST, COURSE_NAME, add_bootcamp_flags)
    if Course.process_generic_commands(args, remargs):
        return
    if args.listrubrics is True:
        if args.uid and args.uid != TEST_STUDENT:
            Course.display_rubric(args.host, args.course, args.uid, args.verbose)
        else:
            Course.display_rubric_ids(args.host, args.course, args.verbose)
        return
    if args.makecurve is True:
        standard = [('A+',2.4,99),('A',1.8,97.5),('A-',1.0,95),
                    ('B+',0.4,91),('B',-0.2,87),('B-',-1.0,83),
                    ('C+',-1.6,77),('C',-2.2,74),('C-',-3.0,70),
                    ('D+',-3.6,67),('D',-4.2,64),('D-',-4.8,60)]
        course = Course(args.host, args.course, verbose = args.verbose)
        course.mail_address(MAIL)
        course.make_curve(standard,SPLIT_STDDEV,args.verbose,args.dryrun,-2.2)
        return
    if args.reassign:
        reassign(args,remargs)
        return

    if args.assignment is None:
        print('You must specify an assignment name with -a')
        return

    if remargs and not args.inclass and not args.homework and not args.shuffle and not args.feedback \
           and not args.zeromissing and not args.makeshuffle \
           and not args.addreviewer \
           and not autodetect(args,remargs[0]):
        print('Unable to auto-detect assignment type.  You must specify a type: -I, -H, -S, or -F')
        return
        
    if args.points is None:
        if args.shuffle:
            args.points = 12
        elif args.feedback:
            args.points = 12
        else:
            args.points = 100
    if args.shuffle or args.feedback:
        args.use_raw_points = True
    else:
        args.use_raw_points = False

    course = Course(HOST, COURSE_NAME, verbose=args.verbose)
    course.simulate(args.dryrun)
    course.mail_address(MAIL)
    course.use_raw_points(args.use_raw_points)
    course.set_points(args.points)
    course.set_late_percentage(LATE_PERCENTAGE,LATE_DAYS)
    course.set_due_day(args.due_day)
    course.find_assignment(args.assignment)
    if course.assignment_id is None:
        return

    if args.addreviewer:
        course.add_peer_reviewer(args.addreviewer,remargs[0])
    elif args.makeshuffle is True:
        make_shuffle(course,args)
    elif args.feedback or args.shuffle:
        if args.old:
            process_shuffle_csv(course,args)
        else:
            process_shuffle_rubric(course,args)
    elif remargs is not None and remargs != []:
        process_grades(course,args,remargs)
    else:
        print("Sending grade of",args.grade,"for UID",args.uid)
        course.upload_grade(args.uid, args.grade, args.message)
    return

if __name__ == "__main__":
    main()
