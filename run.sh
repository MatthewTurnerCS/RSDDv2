#!/bin/bash

cd src
javac FPFuzzer.java
java FPFuzzer > ../out.smt
rm *.class
cd ..

# TODO: need to test on multiple solvers, not just z3
pbcopy < out.smt
cat -n out.smt
echo ""
./z3/bin/z3 -smt2 out.smt

rm out.smt
