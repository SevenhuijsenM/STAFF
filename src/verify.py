"""Verification utilities for Frama-C and Dafny."""

import os
import re
import tempfile
import time
from typing import Dict
from .subprocess_creator import run_command_list

def _materialize_c_file(c_code: str = None, c_file: str = None) -> tuple[str, bool]:
    """Returns a concrete C file path and whether it should be cleaned up."""
    if c_code is not None:
        tmp = tempfile.NamedTemporaryFile(mode="w", suffix=".c", prefix="framac_", delete=False, encoding="utf-8")
        try:
            tmp.write(c_code)
            tmp.flush()
        finally:
            tmp.close()
        return tmp.name, True

    if c_file:
        return c_file, False

    return "", False


def verify_with_wp(c_code: str = None, c_file: str = None, timeout: int = 120, prover: str = "Alt-Ergo") -> Dict:
    """
    Verifies a C file using Frama-C WP.
    
    Args:
        c_code (str): C code string (will be written to temp file).
        c_file (str): Path to C file (alternative to c_code).
        timeout (int): Timeout in seconds.
    
    Returns:
        Dict with verified, proof_obligations, proven, unproven.
    """
    c_path, cleanup = _materialize_c_file(c_code=c_code, c_file=c_file)

    if not c_path or not os.path.exists(c_path):
        return {"verified": False, "proof_obligations": 0, "proven_obligations": 0, "unproven_obligations": 0}

    start_time = time.time()
    try:
        stdout, stderr, _ = run_command_list(
            ["frama-c", "-wp", "-wp-rte", "-wp-prover", prover, c_path],
            timeout=timeout
        )

        output = stdout + stderr

        proved_match = re.search(r'Proved goals:\s*(\d+)\s*/\s*(\d+)', output)
        if proved_match:
            proven = int(proved_match.group(1))
            total = int(proved_match.group(2))
            unproven = total - proven
        else:
            proven = 0
            unproven = 0
            total = 0

        verified = unproven == 0 and total > 0
        return {
            "verified": verified,
            "proof_obligations": total,
            "proven_obligations": proven,
            "unproven_obligations": unproven,
            "verification_time": time.time() - start_time,
            "prover_used": prover,
            "output": output[:2000]
        }
    finally:
        if cleanup and os.path.exists(c_path):
            os.remove(c_path)


def compile_c(c_code: str = None, c_file: str = None, timeout: int = 30) -> tuple:
    """
    Compiles a C file with gcc.
    
    Args:
        c_code (str): C code string (will be written to temp file).
        c_file (str): Path to C file (alternative to c_code).
        timeout (int): Timeout in seconds.
    
    Returns:
        tuple: (success, error_message)
    """
    c_path, cleanup = _materialize_c_file(c_code=c_code, c_file=c_file)

    if not c_path:
        return False, "No code provided"

    try:
        stdout, stderr, success = run_command_list(
            ["gcc", "-c", "-fsyntax-only", c_path],
            timeout=timeout
        )

        output = stdout + stderr
        has_error = "error" in output.lower() and "0 error" not in output.lower()
        return (success and not has_error), stderr
    finally:
        if cleanup and os.path.exists(c_path):
            os.remove(c_path)


def _materialize_dafny_file(dafny_code: str = None, dafny_file: str = None) -> tuple[str, bool]:
    if dafny_code is not None:
        tmp = tempfile.NamedTemporaryFile(mode="w", suffix=".dfy", prefix="dafny_", delete=False, encoding="utf-8")
        try:
            tmp.write(dafny_code)
            tmp.flush()
        finally:
            tmp.close()
        return tmp.name, True

    if dafny_file:
        return dafny_file, False

    return "", False


def compile_dafny(dafny_code: str = None, dafny_file: str = None, timeout: int = 60, dafny_executable: str = "dafny") -> tuple:
    dafny_path, cleanup = _materialize_dafny_file(dafny_code=dafny_code, dafny_file=dafny_file)

    if not dafny_path:
        return False, "No code provided"

    try:
        stdout, stderr, success = run_command_list(
            [dafny_executable, "resolve", dafny_path],
            timeout=timeout,
        )
        output = (stdout + stderr).strip()
        return success, output
    finally:
        if cleanup and os.path.exists(dafny_path):
            os.remove(dafny_path)


def verify_dafny(dafny_code: str = None, dafny_file: str = None, timeout: int = 120, dafny_executable: str = "dafny") -> Dict:
    dafny_path, cleanup = _materialize_dafny_file(dafny_code=dafny_code, dafny_file=dafny_file)

    if not dafny_path or not os.path.exists(dafny_path):
        return {"verified": False, "proof_obligations": 0, "proven_obligations": 0, "unproven_obligations": 0}

    start_time = time.time()
    try:
        stdout, stderr, success = run_command_list(
            [dafny_executable, "verify", dafny_path],
            timeout=timeout,
        )
        output = stdout + stderr
        verified = success and "0 errors" in output
        return {
            "verified": verified,
            "proof_obligations": 0,
            "proven_obligations": 0,
            "unproven_obligations": 0,
            "verification_time": time.time() - start_time,
            "prover_used": dafny_executable,
            "output": output[:2000],
        }
    finally:
        if cleanup and os.path.exists(dafny_path):
            os.remove(dafny_path)
