#!/usr/bin/env python3

# Usage:
# `python3 pretty-print.py input.smt2`
# Reads the input file and pretty-prints the assertions.

import sys

from z3 import *

with open(sys.argv[1], 'r') as file:
    smtlib2_str = file.read()

s = Solver()
s.from_string(smtlib2_str)

for assertion in s.assertions():
    print(assertion)
