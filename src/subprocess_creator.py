"""Subprocess utilities for running shell commands."""

import subprocess
from typing import Tuple


def run_command(command: str, timeout: int = 30, shell: bool = True) -> Tuple[str, str, bool]:
    """
    Runs a shell command with a specified timeout.
    
    Args:
        command (str): The command to execute.
        timeout (int): The maximum time in seconds.
        shell (bool): Whether to run in shell mode.
    
    Returns:
        tuple: (stdout, stderr, success)
    """
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=shell)
    try:
        process.wait(timeout=timeout)
        stdout, stderr = process.communicate()
        return stdout.decode("utf-8"), stderr.decode("utf-8"), True
    except subprocess.TimeoutExpired:
        process.kill()
        return "", "Timeout", False


def run_command_list(args: list, timeout: int = 30) -> Tuple[str, str, bool]:
    """
    Runs a command as a list (no shell).
    
    Args:
        args (list): Command as list of strings.
        timeout (int): Timeout in seconds.
    
    Returns:
        tuple: (stdout, stderr, success)
    """
    try:
        result = subprocess.run(
            args, capture_output=True, text=True, timeout=timeout
        )
        return result.stdout, result.stderr, result.returncode == 0
    except subprocess.TimeoutExpired:
        return "", "Timeout", False
    except FileNotFoundError:
        return "", f"Command not found: {args[0]}", False
