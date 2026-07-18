#!/usr/bin/env python3
"""Setup virtual environment for formalspecc."""

import os
import sys
import subprocess

VENV_DIR = "venv"

def main():
    print("Setting up formalspecc virtual environment...")
    
    # Create virtual environment if it doesn't exist
    if not os.path.exists(VENV_DIR):
        print("Creating virtual environment...")
        subprocess.run([sys.executable, "-m", "venv", VENV_DIR], check=True)
    
    # Determine pip and python paths
    if sys.platform == "win32":
        pip_path = os.path.join(VENV_DIR, "Scripts", "pip.exe")
        python_path = os.path.join(VENV_DIR, "Scripts", "python.exe")
    else:
        pip_path = os.path.join(VENV_DIR, "bin", "pip")
        python_path = os.path.join(VENV_DIR, "bin", "python")
    
    # Upgrade pip using the venv python
    print("Upgrading pip...")
    subprocess.run([python_path, "-m", "pip", "install", "--upgrade", "pip"], check=True)
    
    # Install dependencies
    print("Installing dependencies...")
    subprocess.run([python_path, "-m", "pip", "install", "-r", "requirements.txt"], check=True)
    
    print()
    print("Virtual environment setup complete!")
    print()
    print("To activate the environment, run:")
    if sys.platform == "win32":
        print(f"  {VENV_DIR}\\Scripts\\activate")
    else:
        print(f"  source {VENV_DIR}/bin/activate")
    print()
    print("To run the pipeline:")
    if sys.platform == "win32":
        print(f"  {VENV_DIR}\\Scripts\\python main.py --openai-key YOUR_KEY")
    else:
        print(f"  source {VENV_DIR}/bin/activate && python main.py --openai-key YOUR_KEY")

if __name__ == "__main__":
    main()
