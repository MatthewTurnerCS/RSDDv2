#!/usr/bin/python

import csv
import sys


def main(argv):
  if len(argv) < 1:
    print "must provide a filename to clean up. usage:"
    print "\tpython %s <filename>" % __file__
    return

  filename = argv[0]
  logfile = open(filename, 'r')
  outfile = open(filename + '-cleaned', 'w')

  count = 0
  for line in logfile:
    count += 1
    if count < 4:
      outfile.write(line)
      continue # header stuff
    values = line.split(",")
    if values[1] != values[3]:
      outfile.write(line)
  logfile.close()
  outfile.close()


if __name__ == "__main__":
  main(sys.argv[1:])
