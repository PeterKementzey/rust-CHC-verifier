#!/usr/bin/env python3

import os
import subprocess

def main():
  for file in os.listdir('examples'):
    if file.endswith('.rs'):
      command = f'cargo run examples/{file}'
      print(f'Running: {command}')
      subprocess.run(command, shell=True, check=True)

if __name__ == "__main__":
  main()
