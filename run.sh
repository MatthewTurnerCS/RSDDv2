#!/bin/bash

# compile fuzzer
javac -classpath src src/FPFuzzer.java
java -classpath src FPFuzzer -numFuncs 50 -numPreds 10 -numVars 20 -numConsts 20 -numDerivedFloats 50 -numDerivedBools 20 -maxArgs 10 -maxDepth 6 > out.smt2

mathsat5Sat="$(command time -p ./solvers/mathsat5/bin/mathsat -input=smt2 out.smt2 2>duration.temp)"
mathsat5Time="$(cat duration.temp)"
rm duration.temp

cat -n out.smt2
echo -e "\n$mathsat5Sat,$mathsat5Time" | xargs

rm out.smt2
rm src/*.class
