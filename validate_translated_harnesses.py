"""Compile and run translated Dafny test harnesses against translated C outputs."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


PRIMITIVE_TYPES = {
    "int",
    "size_t",
    "bool",
    "_Bool",
    "double",
    "float",
    "char*",
    "char *",
    "const char*",
    "const char *",
    "const int*",
    "const int *",
    "int*",
    "int *",
}


@dataclass
class ValidationResult:
    task_id: str
    harness_path: str
    solution_path: str
    status: str
    reason: str = ""
    compile_stdout: str = ""
    compile_stderr: str = ""
    run_stdout: str = ""
    run_stderr: str = ""
    exit_code: Optional[int] = None


def camel_to_snake(name: str) -> str:
    s1 = re.sub(r"(.)([A-Z][a-z]+)", r"\1_\2", name)
    s2 = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", s1)
    return s2.replace("__", "_").lower()


def normalize_type(type_name: str) -> str:
    return " ".join(type_name.replace("const", "").split()).replace(" *", "*").strip()


def split_params(params_raw: str) -> List[str]:
    params: List[str] = []
    depth = 0
    start = 0
    for idx, ch in enumerate(params_raw):
        if ch in "(<[":  # type: ignore[operator]
            depth += 1
        elif ch in ")>]":  # type: ignore[operator]
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            params.append(params_raw[start:idx].strip())
            start = idx + 1
    tail = params_raw[start:].strip()
    if tail:
        params.append(tail)
    return params


def parse_signature(line: str) -> Optional[Dict[str, Any]]:
    match = re.search(
        r"extern\s+(?P<ret>[A-Za-z_][\w\s\*\d]*?)\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\((?P<params>[^)]*)\)\s*;",
        line,
    )
    if not match:
        return None
    params: List[Dict[str, str]] = []
    raw_params = match.group("params").strip()
    if raw_params and raw_params != "void":
        for raw in split_params(raw_params):
            if not raw:
                continue
            pieces = raw.rsplit(" ", 1)
            if len(pieces) == 1:
                params.append({"type": normalize_type(pieces[0]), "name": ""})
                continue
            ptype = normalize_type(pieces[0])
            pname = pieces[1].strip()
            if pname.startswith("*"):
                ptype = f"{ptype} *".strip()
                pname = pname.lstrip("*")
            params.append({"type": ptype, "name": pname})
    return {
        "return_type": normalize_type(match.group("ret")),
        "name": match.group("name"),
        "params": params,
    }


def extract_harness_signature(source: str) -> Optional[Dict[str, Any]]:
    for line in source.splitlines():
        if line.strip().startswith("extern "):
            sig = parse_signature(line.strip())
            if sig:
                return sig
    return None


def extract_solution_definitions(source: str) -> List[Dict[str, Any]]:
    pattern = re.compile(
        r"(?P<prefix>(?:static\s+)*)"
        r"(?P<ret>[A-Za-z_][\w\s\*\d]*?)\s+"
        r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*"
        r"\((?P<params>[^)]*)\)\s*\{",
        re.MULTILINE,
    )
    defs: List[Dict[str, Any]] = []
    for match in pattern.finditer(source):
        defs.append(
            {
                "name": match.group("name"),
                "return_type": normalize_type(match.group("ret")),
                "params": [
                    {"type": normalize_type(p.rsplit(" ", 1)[0]), "name": p.rsplit(" ", 1)[-1].lstrip("*")}
                    for p in split_params(match.group("params") or "")
                    if p.strip()
                ],
                "static": "static" in (match.group("prefix") or ""),
            }
        )
    return defs


def choose_solution_definition(public_name: str, defs: List[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
    if not defs:
        return None
    exact = [d for d in defs if d["name"] == public_name]
    if exact:
        return exact[0]
    snake = camel_to_snake(public_name)
    snake_match = [d for d in defs if d["name"] == snake]
    if snake_match:
        return snake_match[0]
    lower = [d for d in defs if d["name"].lower() == public_name.lower()]
    if lower:
        return lower[0]
    if len(defs) == 1:
        return defs[0]
    return None


def is_seq_like(type_name: str) -> bool:
    normalized = normalize_type(type_name)
    return normalized in {"SeqInt", "IntSeq"} or normalized.endswith("Seq")


def is_pointer_like(type_name: str) -> bool:
    normalized = normalize_type(type_name)
    return normalized in {"int*", "int *", "const int*", "const int *"}


def is_scalar_like(type_name: str) -> bool:
    return normalize_type(type_name) in {"int", "size_t", "bool", "_Bool", "double", "float"}


def wrapper_type(type_name: str) -> str:
    normalized = normalize_type(type_name)
    return type_name


def render_wrapper(solution_path: Path, public_sig: Dict[str, Any], internal_sig: Dict[str, Any]) -> str:
    solution_include = solution_path.resolve().as_posix()
    public_name = public_sig["name"]
    internal_name = internal_sig["name"]
    internal_alias = f"{internal_name}__formalspecc_impl"
    public_ret = normalize_type(public_sig["return_type"])
    wrapper_ret = wrapper_type(public_ret)
    internal_ret = normalize_type(internal_sig["return_type"])
    public_params = public_sig["params"]
    internal_params = internal_sig["params"]

    needs_intseq_helper = normalize_type(internal_ret) == "IntSeq" or any(
        normalize_type(param["type"]) == "IntSeq" for param in internal_params
    )
    needs_intarray_helper = any(normalize_type(param["type"]) == "IntArray" for param in internal_params)

    lines = [
        "#include <stdbool.h>",
        "#include <stddef.h>",
        "#include <stdint.h>",
        f"#define {internal_name} {internal_alias}",
        "#define main translated_solution_main",
        f'#include "{solution_include}"',
        "#undef main",
        f"#undef {internal_name}",
        "",
        "typedef struct {",
        "    int *data;",
        "    size_t len;",
        "} SeqInt;",
        "typedef SeqInt IntSeq;",
        "",
        "typedef struct {",
        "    int *data;",
        "    size_t len;",
        "} ArrayInt;",
        "typedef ArrayInt IntArray;",
        "",
    ]
    if needs_intseq_helper:
        lines.extend(
            [
                "",
                "static IntSeq to_IntSeq(SeqInt s) {",
                "    IntSeq out;",
                "    out.data = s.data;",
                "    out.len = (int)s.len;",
                "    return out;",
                "}",
                "",
                "static SeqInt from_IntSeq(IntSeq s) {",
                "    SeqInt out;",
                "    out.data = s.data;",
                "    out.len = (size_t)s.len;",
                "    return out;",
                "}",
            ]
        )
    if needs_intarray_helper:
        lines.extend(
            [
                "",
                "static IntArray to_IntArray(ArrayInt a) {",
                "    IntArray out;",
                "    out.data = a.data;",
                "    out.len = (int)a.len;",
                "    return out;",
                "}",
            ]
        )
    lines.append("")

    param_exprs: List[str] = []
    consumed = 0
    for ip in internal_params:
        itype = normalize_type(ip["type"])
        if consumed >= len(public_params):
            break
        if itype == "IntSeq":
            pname = public_params[consumed]["name"] or f"arg_{consumed}"
            param_exprs.append(f"to_IntSeq((SeqInt){{{pname}.data, {pname}.len}})")
            consumed += 1
        elif itype == "IntArray":
            ptype = normalize_type(public_params[consumed]["type"]) if consumed < len(public_params) else ""
            if ptype in {"ArrayInt", "SeqInt"}:
                pname = public_params[consumed]["name"] or f"arg_{consumed}"
                param_exprs.append(f"to_IntArray((ArrayInt){{{pname}.data, {pname}.len}})")
                consumed += 1
            else:
                if consumed + 1 >= len(public_params):
                    raise ValueError("Unable to map array parameter pair for wrapper")
                data_name = public_params[consumed]["name"] or f"arg_{consumed}"
                len_name = public_params[consumed + 1]["name"] or f"arg_{consumed + 1}"
                param_exprs.append(f"to_IntArray((ArrayInt){{{data_name}, (size_t){len_name}}})")
                consumed += 2
        else:
            pname = public_params[consumed]["name"] or f"arg_{consumed}"
            if itype in {"size_t", "int"} and normalize_type(public_params[consumed]["type"]) in {"size_t", "int"}:
                param_exprs.append(f"({itype}){pname}")
            else:
                param_exprs.append(pname)
            consumed += 1

    if consumed != len(public_params):
        raise ValueError("Wrapper mapping did not consume all public parameters")

    lines.append(f"{wrapper_ret} {public_name}(")
    sig_lines = []
    for param in public_params:
        sig_lines.append(f"    {wrapper_type(param['type'])} {param['name'] or 'arg'}")
    lines.append(",\n".join(sig_lines) + ")")
    lines.append("{")
    call = f"{internal_alias}({', '.join(param_exprs)})"
    if wrapper_ret == "SeqInt" and internal_ret == "IntSeq":
        lines.append(f"    return from_IntSeq({call});")
    elif normalize_type(public_ret) in {"int", "size_t", "bool", "_Bool", "double", "float"}:
        lines.append(f"    return ({public_ret})({call});")
    else:
        lines.append(f"    return {call};")
    lines.append("}")
    lines.append("")
    return "\n".join(lines)


def build_compile_commands(compiler: str, harness_path: Path, solution_path: Path, wrapper_path: Optional[Path], work_dir: Path) -> List[List[str]]:
    exe_name = f"{harness_path.stem}.exe" if sys.platform.startswith("win") else harness_path.stem
    exe_path = work_dir / exe_name
    return [
        [compiler, "-std=c11", str(harness_path), str(wrapper_path or solution_path), "-o", str(exe_path)],
    ]


def run_command(args: List[str]) -> Tuple[int, str, str]:
    completed = subprocess.run(args, capture_output=True, text=True)
    return completed.returncode, completed.stdout, completed.stderr


def validate_pair(harness_path: Path, solution_path: Path, compiler: str, work_dir: Path) -> ValidationResult:
    harness_source = harness_path.read_text(encoding="utf-8")
    solution_source = solution_path.read_text(encoding="utf-8")
    sig = extract_harness_signature(harness_source)
    if not sig:
        return ValidationResult(
            task_id=harness_path.stem,
            harness_path=str(harness_path),
            solution_path=str(solution_path),
            status="failed",
            reason="Could not find extern signature in harness",
        )

    solution_defs = extract_solution_definitions(solution_source)
    chosen = choose_solution_definition(sig["name"], solution_defs)
    if not chosen:
        return ValidationResult(
            task_id=harness_path.stem,
            harness_path=str(harness_path),
            solution_path=str(solution_path),
            status="failed",
            reason=f"Could not map harness function '{sig['name']}' to translated solution",
        )

    work_dir.mkdir(parents=True, exist_ok=True)
    wrapper_path = work_dir / f"{harness_path.stem}_wrapper.c"
    wrapper_path.write_text(render_wrapper(solution_path, sig, chosen), encoding="utf-8")

    exe_name = f"{harness_path.stem}.exe" if sys.platform.startswith("win") else harness_path.stem
    exe_path = work_dir / exe_name
    compile_stdout = []
    compile_stderr = []
    for cmd in build_compile_commands(compiler, harness_path, solution_path, wrapper_path, work_dir):
        if wrapper_path is None and "-c" in cmd:
            code, out, err = run_command(cmd)
            compile_stdout.append(out)
            compile_stderr.append(err)
            if code != 0:
                return ValidationResult(
                    task_id=harness_path.stem,
                    harness_path=str(harness_path),
                    solution_path=str(solution_path),
                    status="failed",
                    reason="Compilation failed",
                    compile_stdout="".join(compile_stdout),
                    compile_stderr="".join(compile_stderr),
                    exit_code=code,
                )
            continue
        code, out, err = run_command(cmd)
        compile_stdout.append(out)
        compile_stderr.append(err)
        if code != 0:
            return ValidationResult(
                task_id=harness_path.stem,
                harness_path=str(harness_path),
                solution_path=str(solution_path),
                status="failed",
                reason="Compilation failed",
                compile_stdout="".join(compile_stdout),
                compile_stderr="".join(compile_stderr),
                exit_code=code,
            )

    run_code, run_out, run_err = run_command([str(exe_path)])
    if run_code != 0:
        return ValidationResult(
            task_id=harness_path.stem,
            harness_path=str(harness_path),
            solution_path=str(solution_path),
            status="failed",
            reason="Harness execution failed",
            compile_stdout="".join(compile_stdout),
            compile_stderr="".join(compile_stderr),
            run_stdout=run_out,
            run_stderr=run_err,
            exit_code=run_code,
        )

    return ValidationResult(
        task_id=harness_path.stem,
        harness_path=str(harness_path),
        solution_path=str(solution_path),
        status="passed",
        compile_stdout="".join(compile_stdout),
        compile_stderr="".join(compile_stderr),
        run_stdout=run_out,
        run_stderr=run_err,
        exit_code=run_code,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate translated harnesses against translated C")
    parser.add_argument("--harness-dir", default="translated-harnesses/MBPP-153-tests")
    parser.add_argument("--solution-dir", default="translated-c/MBPP-DFY-153-fixed")
    parser.add_argument("--compiler", default="gcc")
    parser.add_argument("--report", default="translated-harnesses/harness_validation_report.json")
    parser.add_argument("--work-dir", default="")
    args = parser.parse_args()

    harness_dir = Path(args.harness_dir)
    solution_dir = Path(args.solution_dir)
    if not harness_dir.exists():
        print(f"Harness directory not found: {harness_dir}")
        return 1
    if not solution_dir.exists():
        print(f"Solution directory not found: {solution_dir}")
        return 1

    harness_files = sorted(harness_dir.glob("task_id_*.c"))
    results: List[ValidationResult] = []
    passed = failed = skipped = 0
    base_work_dir = Path(args.work_dir) if args.work_dir else Path("validation-work")
    base_work_dir.mkdir(parents=True, exist_ok=True)

    for harness_path in harness_files:
        solution_path = solution_dir / harness_path.name
        if not solution_path.exists():
            skipped += 1
            results.append(
                ValidationResult(
                    task_id=harness_path.stem,
                    harness_path=str(harness_path),
                    solution_path=str(solution_path),
                    status="skipped",
                    reason="Missing translated solution C file",
                )
            )
            continue

        work_dir = base_work_dir / harness_path.stem
        try:
            result = validate_pair(harness_path, solution_path, args.compiler, work_dir)
        except Exception as err:
            result = ValidationResult(
                task_id=harness_path.stem,
                harness_path=str(harness_path),
                solution_path=str(solution_path),
                status="failed",
                reason=str(err),
            )
        results.append(result)
        if result.status == "passed":
            passed += 1
        elif result.status == "skipped":
            skipped += 1
        else:
            failed += 1
        print(f"[{result.status}] {harness_path.stem}")

    summary = {
        "harness_dir": str(harness_dir.resolve()),
        "solution_dir": str(solution_dir.resolve()),
        "compiler": args.compiler,
        "total": len(results),
        "passed": passed,
        "failed": failed,
        "skipped": skipped,
        "results": [asdict(r) for r in results],
    }

    report_path = Path(args.report)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(f"Passed: {passed}, failed: {failed}, skipped: {skipped}")
    print(f"Report: {report_path}")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
