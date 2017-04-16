#!/usr/bin/python

import csv
import sys


def main(argv):
  if len(argv) < 1:
    print "must provide a filename to analyze. usage:"
    print "\tpython %s <filename>" % __file__
    return

  filename = argv[0]

  if "complete" not in filename:
    print "this isn't a complete experiment log. results will be skewed"
    return

  logfile = open(filename, 'r')

  line_num = 0
  stats = {
    "z3-sat": 0,
    "z3-unsat": 0,
    "z3-timeout": 0,
    "z3-total-user-time": 0.0,
    "z3-max-run-time": 0.0,
    "mathsat-sat": 0,
    "mathsat-unsat": 0,
    "mathsat-timeout": 0,
    "mathsat-total-user-time": 0.0,
    "mathsat-max-run-time": 0.0,
    "z3-mathsat-match": 0,
    "z3-mathsat-no-match": 0,
    "z3-mathsat-non-timeout-no-match": 0,
    "z3-mathsat-non-timeout-no-matches": [],
    "total-iterations": 0,
    "mathsat-sat-when-z3-timeout": 0,
    "mathsat-unsat-when-z3-timeout": 0,
    "mathsat-?-when-z3-timeout": 0,
  }
  for line in logfile:
    line_num += 1
    if line_num < 4:
      continue # header stuff

    try:
      # build up stats from file
      v = line.split(",")
      if v[1] == "sat":
        stats["z3-sat"] += 1
      elif v[1] == "unsat":
        stats["z3-unsat"] += 1
      elif v[1] == "timeout" or v[1] == "":
        stats["z3-timeout"] += 1

      if len(v[2].split()) < 2:
        z3_real_time = 3600.0
      else:
        z3_real_time = float(v[2].split()[1])
        stats["z3-max-run-time"] = max(stats["z3-max-run-time"], z3_real_time)
      stats["z3-total-user-time"] += z3_real_time

      if v[3] == "sat":
        stats["mathsat-sat"] += 1
      elif v[3] == "unsat":
        stats["mathsat-unsat"] += 1
      elif v[3] == "timeout" or v[3] == "":
        stats["mathsat-timeout"] += 1

      if len(v[4].split()) < 2:
        mathsat_real_time = 3600.0
      else:
        mathsat_real_time = float(v[4].split()[1])
        stats["mathsat-max-run-time"] = max(stats["mathsat-max-run-time"], mathsat_real_time)
      stats["mathsat-total-user-time"] += mathsat_real_time

      if v[1] == v[3]:
        stats["z3-mathsat-match"] += 1
      else:
        stats["z3-mathsat-no-match"] += 1
        if v[1] != "timeout" and v[3] != "timeout" and v[1] != "" and v[3] != "":
          stats["z3-mathsat-non-timeout-no-match"] += 1
          stats["z3-mathsat-non-timeout-no-matches"].append(v[0])

      if v[1] == "timeout" or v[1] == "":
        if v[3] == "sat":
          stats["mathsat-sat-when-z3-timeout"] += 1
        elif v[3] == "unsat":
          stats["mathsat-unsat-when-z3-timeout"] += 1
        else:
          stats["mathsat-?-when-z3-timeout"] += 1
    except Exception as e:
      print e, v, "\n"
      continue

    stats["total-iterations"] += 1

  logfile.close()

  print "%s:\t%d"     % ("z3-sat                            ", stats["z3-sat"])
  print "%s:\t%d"     % ("z3-unsat                          ", stats["z3-unsat"])
  print "%s:\t%d"     % ("z3-timeout                        ", stats["z3-timeout"])
  print "%s:\t%0.02f" % ("z3-total-user-time                ", stats["z3-total-user-time"])
  print "%s:\t%0.02f" % ("z3-avg-user-time                  ", stats["z3-total-user-time"] / stats["total-iterations"])
  print "%s:\t%0.02f" % ("z3-max-run-time                   ", stats["z3-max-run-time"])
  print "%s:\t%d"     % ("mathsat-sat                       ", stats["mathsat-sat"])
  print "%s:\t%d"     % ("mathsat-unsat                     ", stats["mathsat-unsat"])
  print "%s:\t%d"     % ("mathsat-timeout                   ", stats["mathsat-timeout"])
  print "%s:\t%0.02f" % ("mathsat-total-user-time           ", stats["mathsat-total-user-time"])
  print "%s:\t%0.02f" % ("mathsat-avg-user-time             ", stats["mathsat-total-user-time"] / stats["total-iterations"])
  print "%s:\t%0.02f" % ("mathsat-max-run-time              ", stats["mathsat-max-run-time"])
  print "%s:\t%d"     % ("z3-mathsat-match                  ", stats["z3-mathsat-match"])
  print "%s:\t%d"     % ("z3-mathsat-no-match               ", stats["z3-mathsat-no-match"])
  print "%s:\t%d"     % ("z3-mathsat-non-timeout-no-match   ", stats["z3-mathsat-non-timeout-no-match"])
  print "%s:\t%s"     % ("z3-mathsat-non-timeout-no-matches ", stats["z3-mathsat-non-timeout-no-matches"])
  print "%s:\t%d"     % ("total-iterations                  ", stats["total-iterations"])
  print "%s:\t%d"     % ("mathsat-sat-when-z3-timeout       ", stats["mathsat-sat-when-z3-timeout"])
  print "%s:\t%d"     % ("mathsat-unsat-when-z3-timeout     ", stats["mathsat-unsat-when-z3-timeout"])
  print "%s:\t%s"     % ("mathsat-?-when-z3-timeout         ", stats["mathsat-?-when-z3-timeout"])


if __name__ == "__main__":
  main(sys.argv[1:])
