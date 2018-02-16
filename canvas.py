#!/bin/env python3

from canvaslms import Course, Grade, CanvasCSV

######################################################################

## configuration
COURSE_NAME = "Coding & Algorithms Bootcamp"
HOST = "canvas.cmu.edu"

######################################################################

def main():
    args, remargs = Course.parse_arguments(HOST, COURSE_NAME)
    if Course.process_generic_commands(args, remargs):
        return
    print('This sample program only supports the built-in display functions from canvaslms.py.',
          'Use canvas.py --help for a list.',sep='\n')
    return

if __name__ == "__main__":
    main()

