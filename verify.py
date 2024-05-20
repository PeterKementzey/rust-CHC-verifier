#!/usr/bin/env python3

# Usage:
# `python3 verify.py [optional list of args]`
# Compiles project, creates smt2 file for each argument from `examples/example<arg>.rs` and runs z3 on
# the created `examples/example<arg>.smt2`.
# If no arguments are provided, it will run on all rust files in the examples directory.


import os
import subprocess
import sys


def print_green(text):
    GREEN = '\033[92m'  # Green text
    ENDC = '\033[0m'  # Reset to the default color
    print(f"{GREEN}{text}{ENDC}")


def verify_example(example):
    source_file_name = example + '.rs'
    smt_file_name = example + '.smt2'
    command = f'./target/debug/rust-verifier examples/{source_file_name}'
    print_green(f'Running: {command}')
    subprocess.run(command, shell=True, check=True)
    print_green(f'Created file {smt_file_name}:')
    with open(f'examples/{smt_file_name}', 'r') as f:
        print(f.read())
    command = f'z3 examples/{smt_file_name}'
    print_green(f'Running: {command}')
    subprocess.run(command, shell=True, check=True)


def main():
    print_green('Running: cargo build')
    subprocess.run('cargo build', shell=True, check=True)

    if len(sys.argv) < 2:
        for file in os.listdir('examples'):
            if file.endswith('.rs'):
                verify_example(file[:-3])
    else:
        for arg in sys.argv[1:]:
            verify_example(f'example{arg}')


if __name__ == "__main__":
    main()
