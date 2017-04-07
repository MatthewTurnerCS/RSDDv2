#!/bin/bash

# compile fuzzer
javac -classpath src src/FPFuzzer.java
java -classpath src FPFuzzer > out.smt2

mathsat5Sat="$(command time -p ./solvers/mathsat5/bin/mathsat -input=smt2 out.smt2 2>duration.temp)"
mathsat5Time="$(cat duration.temp)"
rm duration.temp

# cat out.smt2
echo -e "\n$mathsat5Sat,$mathsat5Time" | xargs

rm out.smt2
rm src/*.class
