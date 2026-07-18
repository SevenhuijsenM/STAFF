"""Round-trip comparison utilities for Dafny -> ACSL -> Dafny workflows."""

from __future__ import annotations

import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any, Dict, List

from .differential_testing import (
    _prepare_dafny_test_source,
    _extract_generated_test_cases,
    _find_adapter_info,
    _find_adapter_method,
    _build_dafny_vector_runner,
    _parse_dafny_literal,
)
from .pipeline import extract_dafny_stats
from .subprocess_creator import run_command_list
from .verify import verify_dafny


def _run_dafny_command(args: List[str], timeout: int) -> Dict[str, Any]:
    stdout, stderr, success = run_command_list(args, timeout=timeout)
    return {
        "success": success,
        "stdout": stdout,
        "stderr": stderr,
        "command": args,
    }


def _remove_comments(text: str) -> str:
    without_block = re.sub(r"/\*.*?\*/", " ", text, flags=re.DOTALL)
    return re.sub(r"//.*", " ", without_block)


def _collapse_ws(text: str) -> str:
    return " ".join((text or "").split()).strip()


def _strip_redundant_outer_parens(text: str) -> str:
    candidate = (text or "").strip()
    while candidate.startswith("(") and candidate.endswith(")"):
        depth = 0
        balanced = True
        for idx, ch in enumerate(candidate):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth < 0:
                    balanced = False
                    break
                if depth == 0 and idx != len(candidate) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        candidate = candidate[1:-1].strip()
    return candidate


def _split_top_level_commas(text: str) -> List[str]:
    parts: List[str] = []
    depth = 0
    start = 0
    for idx, ch in enumerate(text):
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            parts.append(text[start:idx].strip())
            start = idx + 1
    tail = text[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def _parse_named_decls(raw: str) -> List[Dict[str, str]]:
    text = (raw or "").strip()
    if not text:
        return []
    chunks = _split_top_level_commas(text)
    grouped: List[str] = []
    current = ""
    for chunk in chunks:
        if not current:
            current = chunk
        else:
            current = f"{current}, {chunk}"
        if ":" in chunk:
            grouped.append(current)
            current = ""
    if current:
        grouped.append(current)

    decls: List[Dict[str, str]] = []
    for chunk in grouped:
        if ":" not in chunk:
            continue
        names_raw, type_raw = chunk.split(":", 1)
        type_name = _collapse_ws(type_raw)
        for name in [n.strip() for n in names_raw.split(",") if n.strip()]:
            decls.append({"name": name, "type": type_name})
    return decls


def _normalize_clause_expr(expr: str) -> str:
    normalized = _remove_comments(expr)
    normalized = normalized.replace("\r", " ").replace("\n", " ")
    normalized = _collapse_ws(normalized.rstrip(";"))
    for operator in ("<==>", "==>", "=="):
        split = _split_top_level_operator(normalized, operator)
        if split:
            left, right = split
            return f"{_normalize_clause_expr(left)} {operator} {_normalize_clause_expr(right)}"
    normalized = _strip_redundant_outer_parens(normalized)
    return _collapse_ws(normalized)


def _extract_clause_list(text: str, keyword: str) -> List[str]:
    pattern = re.compile(
        rf"\b{keyword}\b\s*(.*?)(?=\b(?:requires|ensures|reads|modifies|decreases)\b|$)",
        flags=re.IGNORECASE | re.DOTALL,
    )
    clauses = []
    for match in pattern.finditer(text):
        clause = _normalize_clause_expr(match.group(1))
        if clause:
            clauses.append(clause)
    return clauses


def _split_top_level_operator(text: str, operator: str) -> tuple[str, str] | None:
    depth = 0
    idx = 0
    limit = len(text) - len(operator)
    while idx <= limit:
        ch = text[idx]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        if depth == 0 and text.startswith(operator, idx):
            return text[:idx].strip(), text[idx + len(operator):].strip()
        idx += 1
    return None


def _extract_dafny_signature_profile(dafny_source: str) -> Dict[str, Any]:
    cleaned = _remove_comments(dafny_source)
    first_body = cleaned.find("{")
    header = cleaned if first_body == -1 else cleaned[:first_body]
    header = header.strip()

    sig_match = re.search(
        r"\b(?P<kind>method|function)\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\((?P<params>[^)]*)\)\s*(?P<rest>.*)$",
        header,
        flags=re.DOTALL,
    )
    if not sig_match:
        return {
            "kind": "",
            "name": "",
            "params": [],
            "returns": [],
            "requires": [],
            "ensures": [],
            "reads": [],
            "modifies": [],
            "decreases": [],
            "canonical": "",
        }

    rest = sig_match.group("rest") or ""
    returns_raw = ""
    function_result_raw = ""
    returns_match = re.match(r"\s*returns\s*\((?P<returns>[^)]*)\)\s*(?P<tail>.*)$", rest, flags=re.DOTALL)
    if returns_match:
        returns_raw = returns_match.group("returns") or ""
        rest = returns_match.group("tail") or ""
    else:
        function_match = re.match(r"\s*:\s*(?P<result>[^{\n]+?)(?P<tail>\s*(?:requires|ensures|reads|modifies|decreases|\{|$).*)$", rest, flags=re.DOTALL)
        if function_match:
            function_result_raw = function_match.group("result") or ""
            rest = function_match.group("tail") or ""

    params = _parse_named_decls(sig_match.group("params") or "")
    param_types = [p["type"] for p in params]
    returns = _parse_named_decls(returns_raw)
    return_types = [r["type"] for r in returns]
    if function_result_raw.strip():
        return_types = [_collapse_ws(function_result_raw)]

    profile = {
        "kind": sig_match.group("kind") or "",
        "name": sig_match.group("name") or "",
        "params": param_types,
        "returns": return_types,
        "requires": sorted(_extract_clause_list(rest, "requires")),
        "ensures": sorted(_extract_clause_list(rest, "ensures")),
        "reads": sorted(_extract_clause_list(rest, "reads")),
        "modifies": sorted(_extract_clause_list(rest, "modifies")),
        "decreases": sorted(_extract_clause_list(rest, "decreases")),
    }
    profile["canonical"] = json.dumps({k: v for k, v in profile.items() if k != "kind"}, sort_keys=True)
    return profile


def _normalize_full_source_text(source: str) -> str:
    return _collapse_ws(_remove_comments(source))


def _generate_cases(prepared_file: str, dafny_executable: str, mode: str, timeout: int) -> Dict[str, Any]:
    res = _run_dafny_command([dafny_executable, "generate-tests", mode, prepared_file], timeout)
    if not res["success"]:
        return {"status": "failed", **res}
    cases = _extract_generated_test_cases(res.get("stdout", ""))
    return {"status": "passed", "cases": cases, **res}


def _run_runner(prepared_file: str, prepared_meta: Dict[str, Any], cases: List[Dict[str, Any]], dafny_executable: str, test_backend: str, timeout: int, work_dir: str) -> Dict[str, Any]:
    if not cases:
        return {"status": "skipped", "reason": "No generated cases"}
    adapter_name = cases[0]["function"]
    adapter_info = _find_adapter_info(prepared_meta, adapter_name)
    if not adapter_info:
        return {"status": "failed", "reason": f"No adapter info found for {adapter_name}"}
    with open(prepared_file, "r", encoding="utf-8") as f:
        prepared_source = f.read()
    adapter_method = _find_adapter_method(prepared_source, adapter_name)
    if not adapter_method:
        return {"status": "failed", "reason": f"No adapter method found for {adapter_name}"}

    runner_source = _build_dafny_vector_runner(prepared_file, adapter_method, cases)
    runner_file = os.path.join(work_dir, Path(prepared_file).stem + ".vector_runner.dfy")
    with open(runner_file, "w", encoding="utf-8") as f:
        f.write(runner_source)

    run_res = _run_dafny_command([dafny_executable, "run", runner_file, "--target", test_backend], timeout)
    if not run_res["success"]:
        return {"status": "failed", "runner_file": runner_file, **run_res}

    outputs = [line.strip() for line in (run_res.get("stdout", "") or "").splitlines() if line.strip()]
    parsed = []
    for line in outputs[-len(cases):]:
        try:
            parsed.append(_parse_dafny_literal(line))
        except Exception:
            parsed.append(line)
    return {"status": "passed", "runner_file": runner_file, "outputs": parsed, **run_res}


def compare_dafny_roundtrip(original_file: str, roundtrip_file: str, dafny_executable: str, generate_tests_mode: str = "InlinedBlock", test_backend: str = "py", timeout: int = 120) -> Dict[str, Any]:
    with open(original_file, "r", encoding="utf-8") as f:
        original_source = f.read()
    with open(roundtrip_file, "r", encoding="utf-8") as f:
        roundtrip_source = f.read()

    work_dir = tempfile.mkdtemp(prefix="roundtrip_compare_")
    original_prepared, original_meta = _prepare_dafny_test_source(original_source, Path(original_file).name, work_dir)
    roundtrip_prepared, roundtrip_meta = _prepare_dafny_test_source(roundtrip_source, Path(roundtrip_file).name, work_dir)

    original_verify = verify_dafny(dafny_file=original_file, dafny_executable=dafny_executable, timeout=timeout)
    roundtrip_verify = verify_dafny(dafny_file=roundtrip_file, dafny_executable=dafny_executable, timeout=timeout)

    generated = _generate_cases(original_prepared, dafny_executable, generate_tests_mode, timeout)
    cases = generated.get("cases", []) if generated.get("status") == "passed" else []

    original_runner = _run_runner(original_prepared, original_meta, cases, dafny_executable, test_backend, timeout, work_dir)
    roundtrip_runner = _run_runner(roundtrip_prepared, roundtrip_meta, cases, dafny_executable, test_backend, timeout, work_dir)

    outputs_match = False
    if original_runner.get("status") == "passed" and roundtrip_runner.get("status") == "passed":
        outputs_match = original_runner.get("outputs", []) == roundtrip_runner.get("outputs", [])

    original_profile = _extract_dafny_signature_profile(original_source)
    roundtrip_profile = _extract_dafny_signature_profile(roundtrip_source)
    spec_equivalent = bool(original_profile.get("canonical")) and original_profile.get("canonical") == roundtrip_profile.get("canonical")

    exact_match = original_source == roundtrip_source
    raw_text_match = original_source.strip() == roundtrip_source.strip()
    normalized_text_match = _normalize_full_source_text(original_source) == _normalize_full_source_text(roundtrip_source)

    original_stats = extract_dafny_stats(original_source)
    roundtrip_stats = extract_dafny_stats(roundtrip_source)
    stat_deltas = {k: roundtrip_stats.get(k, 0) - original_stats.get(k, 0) for k in sorted(set(original_stats) | set(roundtrip_stats))}

    return {
        "original_file": os.path.abspath(original_file),
        "roundtrip_file": os.path.abspath(roundtrip_file),
        "work_dir": work_dir,
        "original_verify": original_verify,
        "roundtrip_verify": roundtrip_verify,
        "generated_tests": generated,
        "original_runner": original_runner,
        "roundtrip_runner": roundtrip_runner,
        "outputs_match": outputs_match,
        "exact_match": exact_match,
        "raw_text_match": raw_text_match,
        "normalized_text_match": normalized_text_match,
        "original_profile": original_profile,
        "roundtrip_profile": roundtrip_profile,
        "spec_equivalent": spec_equivalent,
        "original_stats": original_stats,
        "roundtrip_stats": roundtrip_stats,
        "stat_deltas": stat_deltas,
        "backtranslation_checks": {
            "dafny_verify": {
                "original": original_verify,
                "roundtrip": roundtrip_verify,
                "passed": bool(original_verify.get("verified")) and bool(roundtrip_verify.get("verified")),
            },
            "test_cases": {
                "generated_cases": generated,
                "original_runner": original_runner,
                "roundtrip_runner": roundtrip_runner,
                "passed": bool(original_runner.get("status") == "passed" and roundtrip_runner.get("status") == "passed" and outputs_match),
            },
            "exact_match": {
                "raw": exact_match,
                "normalized": normalized_text_match,
                "passed": exact_match,
            },
        },
        "roundtrip_match": bool(original_verify.get("verified")) and bool(roundtrip_verify.get("verified")) and outputs_match,
        "strict_roundtrip_match": bool(original_verify.get("verified")) and bool(roundtrip_verify.get("verified")) and outputs_match and exact_match,
    }


def _find_roundtrip_candidate(roundtrip_root: Path, filename: str) -> Path | None:
    direct = roundtrip_root / filename
    if direct.exists():
        return direct

    candidates = [p for p in roundtrip_root.rglob(filename) if p.is_file()]
    if not candidates:
        return None

    preferred_dirs = ("non_compiling", "non_verifying", "verified", "initial")

    def sort_key(path: Path) -> tuple[int, int, str]:
        try:
            rel = path.relative_to(roundtrip_root)
        except ValueError:
            rel = path
        parts = set(rel.parts[:-1])
        for idx, marker in enumerate(preferred_dirs):
            if marker in parts:
                return (idx, len(rel.parts), str(path))
        return (len(preferred_dirs), len(rel.parts), str(path))

    return sorted(candidates, key=sort_key)[0]


def compare_directories(original_dir: str, roundtrip_dir: str, dafny_executable: str, out_dir: str, generate_tests_mode: str = "InlinedBlock", test_backend: str = "py", timeout: int = 120) -> Dict[str, Any]:
    orig = Path(original_dir)
    rt = Path(roundtrip_dir)
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)

    results = []
    for original_file in sorted(orig.glob("task_id_*.dfy")):
        rt_file = _find_roundtrip_candidate(rt, original_file.name)
        if not rt_file:
            results.append({
                "original_file": str(original_file),
                "roundtrip_file": str(rt / original_file.name),
                "missing_roundtrip": True,
                "roundtrip_match": False,
            })
            continue
        results.append(compare_dafny_roundtrip(str(original_file), str(rt_file), dafny_executable, generate_tests_mode, test_backend, timeout))

    summary = {
        "total": len(results),
        "matched": sum(1 for r in results if r.get("roundtrip_match")),
        "strict_matched": sum(1 for r in results if r.get("strict_roundtrip_match")),
        "spec_equivalent": sum(1 for r in results if r.get("spec_equivalent")),
        "exact_match": sum(1 for r in results if r.get("exact_match")),
        "raw_text_match": sum(1 for r in results if r.get("raw_text_match")),
        "normalized_text_match": sum(1 for r in results if r.get("normalized_text_match")),
        "verified_both": sum(1 for r in results if r.get("original_verify", {}).get("verified") and r.get("roundtrip_verify", {}).get("verified")),
        "output_match": sum(1 for r in results if r.get("outputs_match")),
        "missing_roundtrip": sum(1 for r in results if r.get("missing_roundtrip")),
        "results": results,
    }
    with open(out / "roundtrip_summary.json", "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
    md = [
        f"# Round-trip summary",
        "",
        f"- Total files compared: {summary['total']}",
        f"- Specification-equivalent files: {summary['spec_equivalent']}",
        f"- Exact text matches: {summary['exact_match']}",
        f"- Raw text matches: {summary['raw_text_match']}",
        f"- Normalized text matches: {summary['normalized_text_match']}",
        f"- Verified on both sides: {summary['verified_both']}",
        f"- Behavioral output matches: {summary['output_match']}",
        f"- Full round-trip matches: {summary['matched']}",
        f"- Strict full round-trip matches: {summary['strict_matched']}",
        f"- Missing round-trip files: {summary['missing_roundtrip']}",
    ]
    with open(out / "roundtrip_summary.md", "w", encoding="utf-8") as f:
        f.write("\n".join(md) + "\n")
    return summary
