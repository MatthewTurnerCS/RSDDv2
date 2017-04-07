#!/bin/bash

# compile fuzzer
javac -classpath src src/FPFuzzer.java

# create a logs directory if it doesn't already exist
mkdir -p logs

# prepare the log files
echo -e "the generated formulas used by the solvers\n" > logs/fuzzes.log
echo -e "an overview of the results of each solver\n" > logs/fuzzes_complete.log
echo -e "results when a solver crashed or had inconsistencies\n" > logs/fuzzes_error.log
echo -e "iteration,z3-crash,z3-sat,z3-time,mathsat-crash,mathsat-sat,mathsat-time" >> logs/fuzzes_complete.log
echo -e "iteration,z3-crash,z3-sat,z3-time,mathsat-crash,mathsat-sat,mathsat-time" >> logs/fuzzes_error.log

TIMEOUT=3600 # 1 hour

# iterate a bunch
for i in {1..50000}
do
  # generate a new formula
  java -classpath src FPFuzzer > out.smt2

  # log the newly generated thing to be able to easily find should a
  # discrepency between solvers occur
  echo -e "\n\n-- iteration $i --" >> logs/fuzzes.log
  cat out.smt2 >> logs/fuzzes.log

  # run the solvers on the newly generated formulas
  # run z3 to get "sat" or "unsat" with runtime written to file
  z3Sat="$(command time -p ./solvers/z3/bin/z3 -smt2 -T:$TIMEOUT out.smt2 2>duration.temp | xargs)"
  z3Time="$(cat duration.temp)"
  rm duration.temp

  # run mathsat5 to get "sat" or "unsat" with runtime written to file
  # note: mathsat5 doesn't have a timeout option :(
  mathsat5Sat="$(command time -p ./solvers/mathsat5/bin/mathsat -input=smt2 out.smt2 2>duration.temp | xargs)"
  mathsat5Time="$(cat duration.temp)"
  rm duration.temp

  # if there was an error or an inconsistency, log it in errors
  if ([ "$z3Sat" != "sat" ] && [ "$z3Sat" != "unsat" ]) || ([ "$mathsat5Sat" != "sat" ] && [ "$mathsat5Sat" != "unsat" ]) || [ "$mathsat5Sat" != "$z3Sat" ]; then
    echo -e "$i,$z3Sat,$z3Time,$mathsat5Sat,$mathsat5Time" | xargs >> logs/fuzzes_error.log
  fi

  # log results for each run of the solver
  echo -e "$i,$z3Sat,$z3Time,$mathsat5Sat,$mathsat5Time" | xargs >> logs/fuzzes_complete.log
done

# cleanup
# remove class files
rm out.smt2
rm src/*.class
