#!/usr/bin/env python3

# Usage:
# `python3 verify.py [optional list of rust files]`
#
# This scipt:
#
# 1. Compiles project
# 2. Creates smt2 file with Constrained Horn Clauses from each argument
# 3. Runs Z3 to check satisfiability of each smt2 file
#
# If no arguments are provided, it will run on all rust files in the examples directory.


import os
import subprocess
import sys


def print_green(text):
    GREEN = '\033[92m'  # Green text
    ENDC = '\033[0m'  # Reset to the default color
    print(f"{GREEN}{text}{ENDC}")

def run_command(command: str):
    print_green(f'Running: {command}')
    subprocess.run(command, shell=True, check=True)


def verify_example(example: str):
    source_file_name = example
    smt_file_name = example[:-3] + '.smt2'

    print_green(f'Verifying {source_file_name}:')
    with open(source_file_name, 'r') as f:
        print(f.read())

    run_command(f'./target/release/rust-verifier {source_file_name}')

    print_green(f'Created file {smt_file_name}:')
    with open(f'{smt_file_name}', 'r') as f:
        print(f.read())

    run_command(f'python3 pretty-print-assertions.py {smt_file_name}')

    run_command(f'z3 {smt_file_name}')


def main():
    run_command('cargo build --release')

    if len(sys.argv) < 2:
        for file in os.listdir('examples'):
            if file.endswith('.rs'):
                verify_example(f'examples/{file}')
    else:
        for arg in sys.argv[1:]:
            verify_example(arg)


if __name__ == "__main__":
    main()
