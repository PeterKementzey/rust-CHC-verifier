#!/usr/bin/env python3

import os
import subprocess

# Define color codes
GREEN = '\033[92m' # Green text
ENDC = '\033[0m' # Reset to the default color

def print_green(text):
    print(f"{GREEN}{text}{ENDC}")

def main():
  print_green('Running: cargo build')
  subprocess.run('cargo build', shell=True, check=True)

  for file in os.listdir('examples'):
    if file.endswith('.rs'):
      command = f'./target/debug/rust-verifier examples/{file}'
      print_green(f'Running: {command}')
      subprocess.run(command, shell=True, check=True)
      # print the smt2 file
      print_green(f'Created file {file[:-3]}.smt2:')
      with open(f'examples/{file[:-3]}.smt2', 'r') as f:
        print(f.read())
      command = f'z3 examples/{file[:-3]}.smt2'
      print_green(f'Running: {command}')
      subprocess.run(command, shell=True, check=True)

if __name__ == "__main__":
  main()
