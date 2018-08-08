#!/bin/env python3

##  by Ralf Brown, Carnegie Mellon University
##  last edit: 02may2018

######################################################################
####    Institution-specific functionality			  ####

class Institution():
    def __init__(self):
        return

    @staticmethod
    def add_institution_flags(parser):
        '''
        add the flags specific to CMU to the given argument parser
        '''
        parser.add_argument("--s3grades_mid",action="store_true",help="insert midterm grades into S3 CSV file")
        parser.add_argument("--s3grades_final",action="store_true",help="insert final grades into S3 CSV file")
        return

    @staticmethod
    def process_generic_commands(args, remargs):
        if args.s3grades_mid is True:
            pass
        if args.s3grades_final is True:
            pass
        # if we get down to here, there was no command handled by this function, so tell our caller it still
        #   needs to handle the commandline
        return False

######################################################################

if __name__ == '__main__':
    print('This module is not intended to be run standalone.')

### end of file canvascmu.py ###
