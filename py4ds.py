#!/bin/env python3

##  by Ralf Brown, Carnegie Mellon University
##  last edit: 15feb2026

import csv
#import datetime
#import dateutil.parser
import math
#import os
#import pytz
#import re
#import sys
import urllib, urllib.request

from canvaslms import Course, Grade, CanvasCSV
from canvascmu import Institution

######################################################################

## configuration
COURSE_NAME = "Python for Data Science"
COURSE_ID = 50675
HOST = "canvas.cmu.edu"
MAIL = "@andrew.cmu.edu"

## configuration of late penalty: percent per day and maximum days late accepted
LATE_PERCENTAGE = 10
LATE_DAYS = 7

######################################################################

def add_py4ds_flags(parser):
    '''
    add the flags specific to 11-604/605 to the given argument parser
    '''
    parser.add_argument("-H","--homework",action="store_true",help="interpret CSV file as a homework assignment")
    parser.add_argument("-E","--exam",action="store_true",help="treat assignment as an exam, use actual points as grade")
    parser.add_argument("--week",metavar="WEEK",help="extract scores for week WEEK from CSV grades file")
    return

######################################################################

def setup_course(args):
    course = Course(HOST, COURSE_NAME, verbose=args.verbose, course_id=COURSE_ID)
    course.simulate(args.dryrun)
    course.mail_address(MAIL)
    course.use_raw_points(args.use_raw_points)
    course.set_points(args.points)
    course.set_late_percentage(LATE_PERCENTAGE,LATE_DAYS)
    course.set_due_day(args.due_day)
    course.find_assignment(args.assignment)
    return course

######################################################################

def parse_nbgrader(course, csv, grades, weeknum, verbose=False):
    ## extract the column numbers of interest from the first row
    row = csv.next_row()
    partnum = 0
    idx_assignment = csv.get_index('assignment')
    idx_andrew = csv.get_index('student_id')
    idx_score = csv.get_index('score')
    idx_late = csv.get_index('late_submission_penalty')  # was the assignment late?
    while not csv.eof:
        row = csv.next_row()
        if not row:
            break
        andrew = csv.get_field(idx_andrew)
        assignment = csv.get_field(idx_assignment)
        (_, _, assignment) = assignment.partition("_") if assignment else (None, None, assignment)
        if assignment != str(weeknum):
            if verbose:
                print('skipping',assignment,'for',andrew)
            continue
        try:
            late_penalty = float(csv.get_field(idx_late)) if idx_late >= 0 else 0
        except:
            late_penalty = 0.0
        email = csv.get_field(idx_andrew) + MAIL
        total = csv.get_field(idx_score)
        uid = course.get_student_id(email,andrew)
        if uid is None:
            continue	# non-existent or dropped student
        comment = ""
        if uid in grades:
            gr = grades[uid]
        else:
            gr = Grade()
            grades[uid] = gr
        if verbose:
            print('   adding',uid,partnum,email,total,comment)
        if total is not None:
            pn = partnum if partnum >= 0 else 0
            gr.add(total,comment,pn,late_penalty)
    return

######################################################################

def process_grades(course, flags, csv_files):
    grades = {}
    for (i, csv_file) in enumerate(csv_files):
        with open(csv_file,"r") as f:
            csvfile = CanvasCSV(f)
            if flags.homework or flags.exam:
                print('processing',csv_file)
                parse_nbgrader(course,csvfile,grades,flags.week,flags.verbose)
    if flags.homework:
        numparts = len(csv_files)
    else:
        numparts = 1
    course.batch_upload_grades(grades,numparts)
    return

######################################################################

def main():
    args, remargs = Course.parse_arguments(HOST, COURSE_NAME,
                                           [Institution.add_institution_flags, add_py4ds_flags])
    if Course.process_generic_commands(args, remargs, course_id=COURSE_ID):
        return
    if Institution.process_generic_commands(args, remargs):
        return
    args.use_raw_points = False

    if args.assignment is None:
        print('You must specify an assignment name with -a')
        return

    if remargs and not args.homework and not args.exam and not args.zeromissing:
        print('Unable to auto-detect assignment type.  You must specify a type: -E or -H')
        return
        
    if args.points is None:
        args.points = 100
    if args.exam:
        args.use_raw_points = True

    course = setup_course(args)
    if course.assignment_id is None:
        return

    if not course.assignment_id:
        print("Not doing anything, because the assignment was 'None' or not found")
        return
    if remargs is not None and remargs != []:
        process_grades(course,args,remargs)
    else:
        print("Sending grade of",args.grade,"for UID",args.uid)
        course.upload_grade(args.uid, args.grade, args.message)
    return

if __name__ == "__main__":
    main()
