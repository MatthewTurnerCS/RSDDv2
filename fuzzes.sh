#!/bin/bash

# compile fuzzer
javac -classpath src src/FPFuzzer.java

# create a logs directory if it doesn't already exist
mkdir -p logs

# prepare the log files
echo -e "the generated formulas used by the solvers\n" > logs/fuzzes.log
echo -e "an overview of the results of each solver\n" > logs/fuzzes_complete.log
echo -e "results when a solver crashed or inconsistencies\n" > logs/fuzzes_error.log
echo -e "iteration\tz3-crash\tz3-sat" >> logs/fuzzes_complete.log
echo -e "iteration\tz3-crash\tz3-sat" >> logs/fuzzes_error.log

# iterate a bunch
for i in {1..1}
do
  # generate a new formula
  java -classpath src FPFuzzer > out.smt2

  # log the newly generated thing to be able to easily find should a
  # discrepency between solvers occur
  echo -e "\n\n-- iteration $i --" >> logs/fuzzes.log
  cat out.smt2 >> logs/fuzzes.log

  # run the solvers on the newly generated formulas
  z3Out="$(./solvers/z3/bin/z3 -smt2 out.smt2)" # "sat" or "unsat"
  z3Res=$? # process ran successfully (0) or crashed (anything else)

  # if there was an error or an inconsistency, log it in errors
  if [ $z3Res -ne 0 ]; then
    echo -e "$i\t$z3Res\t$z3Out" >> logs/fuzzes_error.log
  fi

  # log results for each run of the solver
  echo -e "$i\t$z3Res\t$z3Out" >> logs/fuzzes_complete.log
done

# cleanup
# remove class files
rm out.smt2
rm src/*.class