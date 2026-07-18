"""Post-translation analysis tool."""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Any
from dataclasses import dataclass

from src.subprocess_creator import run_command_list


@dataclass
class CodeStats:
    """Statistics for a code file."""
    filename: str
    lines: int
    functions: int
    requires: int
    ensures: int
    loop_invariant: int
    loop_variant: int
    assigns: int
    asserts: int


def extract_dafny_stats(code: str) -> dict:
    """Extract stats from Dafny code."""
    return {
        "requires": len(re.findall(r'\brequires\b', code)),
        "ensures": len(re.findall(r'\bensures\b', code)),
        "invariant": len(re.findall(r'\binvariant\b', code)),
        "decreases": len(re.findall(r'\bdecreases\b', code)),
        "modifies": len(re.findall(r'\bmodifies\b', code)),
    }


def extract_c_stats(code: str, filename: str) -> CodeStats:
    """Extract ACSL statistics from C code."""
    lines = len(code.splitlines())
    funcs = len(re.findall(r'\b(int|void|bool|char|float|double|long|short|unsigned)\s+\w+\s*\([^)]*\)\s*\{', code))
    requires = len(re.findall(r'/\*\s*@\s*requires|//\s*@\s*requires', code))
    ensures = len(re.findall(r'/\*\s*@\s*ensures|//\s*@\s*ensures', code))
    loop_invariant = len(re.findall(r'/\*\s*@\s*loop\s+invariant|//\s*@\s*loop\s+invariant', code))
    loop_variant = len(re.findall(r'/\*\s*@\s*loop\s+variant|//\s*@\s*loop\s+variant', code))
    assigns = len(re.findall(r'/\*\s*@\s*assigns|//\s*@\s*assigns', code))
    asserts = len(re.findall(r'/\*\s*@\s*assert|//\s*@\s*assert', code))
    return CodeStats(filename, lines, funcs, requires, ensures, loop_invariant, loop_variant, assigns, asserts)


def verify_file(c_file: str, timeout: int = 60, use_rte: bool = True) -> Dict:
    """Run Frama-C WP on a file."""
    cmd = ["frama-c", "-wp", "-wp-prover", "Alt-Ergo"]
    if use_rte:
        cmd.insert(2, "-wp-rte")
    cmd.append(c_file)
    
    stdout, stderr, success = run_command_list(cmd, timeout=timeout)
    output = stdout + stderr
    
    proven = unproven = 0
    m = re.search(r"Proved goals:\s*(\d+)\s*/\s*(\d+)", output)
    if m:
        proven = int(m.group(1))
        unproven = int(m.group(2)) - proven
    else:
        proven = len([l for l in output.split('\n') if 'Goal' in l and 'Proved' in l])
        unproven = len([l for l in output.split('\n') if 'Goal' in l and ('Unproved' in l or 'Failed' in l)])
    
    return {"verified": unproven == 0, "proven": proven, "unproven": unproven, "total": proven + unproven}


def analyze_folder(input_dir: str, output_dir: str, run_verification: bool = False, use_rte: bool = True) -> Dict:
    """Analyze translations in a folder."""
    results = {"input_dir": input_dir, "output_dir": output_dir, "verification_run": run_verification, "use_rte": use_rte, "files": [], "summary": {}}
    
    if not os.path.exists(input_dir):
        print(f"Input folder not found: {input_dir}")
        return results
    if not os.path.exists(output_dir):
        print(f"Output folder not found: {output_dir}")
        return results
    
    dfy_files = sorted([f for f in os.listdir(input_dir) if f.endswith('.dfy')])
    print(f"Analyzing {len(dfy_files)} files...")
    
    for i, dfy_file in enumerate(dfy_files):
        base = os.path.splitext(dfy_file)[0]
        
        with open(os.path.join(input_dir, dfy_file), 'r') as f:
            original = f.read()
        
        dafny_stats = extract_dafny_stats(original)
        
        translated_path = None
        for subdir in ["", "non_verifying", "non_compiling"]:
            candidate = os.path.join(output_dir, subdir, f"{base}.c")
            if os.path.exists(candidate):
                translated_path = candidate
                break
        
        if not translated_path:
            results["files"].append({"base": base, "status": "missing", "dafny_stats": dafny_stats, "c_stats": None, "verification": None})
            continue
        
        with open(translated_path, 'r') as f:
            translated = f.read()
        
        c_stats = extract_c_stats(translated, os.path.basename(translated_path))
        
        status = "verified"
        if "non_compiling" in translated_path:
            status = "non_compiling"
        elif "non_verifying" in translated_path:
            status = "non_verifying"
        
        verification = None
        if run_verification and status != "non_compiling":
            print(f"  [{i+1}/{len(dfy_files)}] Verifying {base}...")
            verification = verify_file(translated_path, use_rte=use_rte)
            if verification["verified"]:
                status = "verified"
            else:
                status = "non_verifying"
        
        results["files"].append({"base": base, "status": status, "dafny_stats": dafny_stats, "c_stats": c_stats.__dict__, "verification": verification})
    
    # Summary
    total = len(results["files"])
    verified = sum(1 for f in results["files"] if f["status"] == "verified")
    non_verifying = sum(1 for f in results["files"] if f["status"] == "non_verifying")
    non_compiling = sum(1 for f in results["files"] if f["status"] == "non_compiling")
    missing = sum(1 for f in results["files"] if f["status"] == "missing")
    
    v = results["summary"].get("verification", {})
    if run_verification:
        v = {"total_proof_obligations": sum(f["verification"]["total"] for f in results["files"] if f["verification"]),
             "proven": sum(f["verification"]["proven"] for f in results["files"] if f["verification"]),
             "unproven": sum(f["verification"]["unproven"] for f in results["files"] if f["verification"]),
             "proven_percentage": 0}
        if v["total_proof_obligations"]:
            v["proven_percentage"] = (v["proven"] / v["total_proof_obligations"]) * 100
    
    total_requires = sum(f["c_stats"]["requires"] for f in results["files"] if f["c_stats"])
    total_ensures = sum(f["c_stats"]["ensures"] for f in results["files"] if f["c_stats"])
    total_invariants = sum(f["c_stats"]["loop_invariant"] for f in results["files"] if f["c_stats"])
    
    total_dfy_requires = sum(f["dafny_stats"]["requires"] for f in results["files"])
    total_dfy_ensures = sum(f["dafny_stats"]["ensures"] for f in results["files"])
    total_dfy_invariants = sum(f["dafny_stats"]["invariant"] for f in results["files"])
    
    results["summary"] = {"total": total, "verified": verified, "non_verifying": non_verifying, "non_compiling": non_compiling, "missing": missing,
                         "dafny_requires": total_dfy_requires, "dafny_ensures": total_dfy_ensures, "dafny_invariants": total_dfy_invariants,
                         "c_requires": total_requires, "c_ensures": total_ensures, "c_invariants": total_invariants,
                         "requires_per_file": total_requires / max(total - missing, 1), "ensures_per_file": total_ensures / max(total - missing, 1),
                         "verification": v}
    
    return results


def print_report(results: Dict):
    s = results["summary"]
    v = s.get("verification", {})
    
    print("=" * 60)
    print("TRANSLATION ANALYSIS REPORT")
    print("=" * 60)
    print(f"Input:  {results['input_dir']}")
    print(f"Output: {results['output_dir']}")
    print()
    print("SUMMARY")
    print("-" * 40)
    print(f"Total files:      {s['total']}")
    print(f"  ✓ Verified:    {s['verified']}")
    print(f"  ~ Non-verify:  {s['non_verifying']}")
    print(f"  ✗ Non-compile: {s['non_compiling']}")
    print(f"  ? Missing:     {s['missing']}")
    
    if v:
        print()
        print("VERIFICATION (Frama-C WP + RTE)" if results.get("use_rte") else "VERIFICATION (Frama-C WP)")
        print("-" * 40)
        print(f"Proof obligations: {v['proven']} / {v['total_proof_obligations']}")
        print(f"Proven:            {v['proven_percentage']:.1f}%")
    
    print()
    print("DAFNY vs ACSL COMPARISON")
    print("-" * 60)
    print(f"{'File':<18} {'Dfy Req':>8} {'C Req':>8} {'Dfy Ens':>8} {'C Ens':>8} {'Dfy Inv':>8} {'C Inv':>8}")
    print("-" * 60)
    
    for f in sorted(results["files"], key=lambda x: x["base"]):
        if f["status"] == "missing":
            continue
        ds = f.get("dafny_stats", {})
        ts = f.get("c_stats", {}) or {}
        print(f"{f['base']:<18} {ds.get('requires', 0):>8} {ts.get('requires', 0):>8} {ds.get('ensures', 0):>8} {ts.get('ensures', 0):>8} {ds.get('invariant', 0):>8} {ts.get('loop_invariant', 0):>8}")
    
    print()
    print("TOTALS")
    print("-" * 40)
    print(f"Dafny requires:  {s['dafny_requires']}")
    print(f"ACSL requires:   {s['c_requires']}")
    print(f"Dafny ensures:   {s['dafny_ensures']}")
    print(f"ACSL ensures:    {s['c_ensures']}")
    print(f"Dafny invariants: {s['dafny_invariants']}")
    print(f"ACSL invariants: {s['c_invariants']}")


def save_report(results: Dict, output_path: str):
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved to: {output_path}")


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Analyze translations")
    parser.add_argument("--input", required=True, help="Input folder (.dfy files)")
    parser.add_argument("--output", required=True, help="Output folder (.c files)")
    parser.add_argument("--verify", action="store_true", help="Run Frama-C verification")
    parser.add_argument("--no-rte", action="store_true", help="Don't use RTE")
    parser.add_argument("--save", help="Save JSON report")
    args = parser.parse_args()
    
    results = analyze_folder(args.input, args.output, run_verification=args.verify, use_rte=not args.no_rte)
    print_report(results)
    if args.save:
        save_report(results, args.save)


if __name__ == "__main__":
    main()
