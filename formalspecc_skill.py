#!/usr/bin/env python3
"""Project-local "skill" utilities for running and analyzing formalspecc.

This script provides reproducible commands to:
- run the pipeline for any dataset folder,
- summarize outputs for paper/reporting,
- generate lightweight SVG figures from run metrics.
"""

from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

from src.roundtrip import compare_directories


_API_KEY_PLACEHOLDER_MARKERS = (
    "your_key",
    "your-api-key",
    "your_api_key",
    "replace_with",
    "sk-...",
    "<your",
)


def _looks_like_placeholder_api_key(value: str) -> bool:
    normalized = value.strip().lower()
    if not normalized:
        return False
    return any(marker in normalized for marker in _API_KEY_PLACEHOLDER_MARKERS)


def _read_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def _ensure_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def _safe_pct(numer: int, denom: int) -> float:
    if denom <= 0:
        return 0.0
    return (100.0 * numer) / float(denom)


def _run_cmd(cmd: list[str], cwd: Path) -> int:
    print("[run]", " ".join(cmd))
    proc = subprocess.run(cmd, cwd=str(cwd), check=False)
    return proc.returncode


def _default_run_label(dataset: str, model: str) -> str:
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    model_slug = model.replace(".", "").replace("/", "-")
    return f"{dataset}-{model_slug}-{stamp}"


def command_run(args: argparse.Namespace) -> int:
    root = Path(__file__).resolve().parent

    api_key = (args.openai_key or os.environ.get("OPENAI_API_KEY") or "").strip()
    if not api_key:
        print("Error: OPENAI_API_KEY is not set (or pass --openai-key).", file=sys.stderr)
        return 2
    if _looks_like_placeholder_api_key(api_key):
        print(
            "Error: OPENAI_API_KEY looks like a placeholder value; set a real API key before running.",
            file=sys.stderr,
        )
        return 2

    out_root = Path(args.output_root)
    output_folder = args.output_folder or _default_run_label(args.dataset, args.model)
    cmd = [
        sys.executable,
        "main.py",
        "--input-folder",
        args.dataset,
        "--output-folder",
        output_folder,
        "--output-dir",
        str(out_root),
        "--model",
        args.model,
        "--temperature",
        str(args.temperature),
        "--checkpoint-every",
        str(args.checkpoint_every),
        "--max-verify-iters",
        str(args.max_verify_iters),
        "--resume",
        "--no-open-report",
    ]

    if args.skip_verification:
        cmd.append("--skip-verification")
    if getattr(args, "enable_differential_testing", False):
        cmd.append("--enable-differential-testing")
    if getattr(args, "skip_roundtrip", False):
        cmd.append("--skip-roundtrip")
    if getattr(args, "dafny_executable", ""):
        cmd.extend(["--dafny-executable", args.dafny_executable])
    if getattr(args, "dafny_backend", ""):
        cmd.extend(["--dafny-backend", args.dafny_backend])
    if getattr(args, "dafny_generate_tests_mode", ""):
        cmd.extend(["--dafny-generate-tests-mode", args.dafny_generate_tests_mode])
    if getattr(args, "dafny_test_backend", ""):
        cmd.extend(["--dafny-test-backend", args.dafny_test_backend])
    if getattr(args, "c_compiler", ""):
        cmd.extend(["--c-compiler", args.c_compiler])
    if getattr(args, "dtest_command_template", ""):
        cmd.extend(["--dtest-command-template", args.dtest_command_template])
    if getattr(args, "dafny_build_command_template", ""):
        cmd.extend(["--dafny-build-command-template", args.dafny_build_command_template])
    if getattr(args, "dafny_generated_tests_command_template", ""):
        cmd.extend(["--dafny-generated-tests-command-template", args.dafny_generated_tests_command_template])
    if getattr(args, "translated_harness_dir", ""):
        cmd.extend(["--translated-harness-dir", args.translated_harness_dir])
    if getattr(args, "enable_mutation_testing", False):
        cmd.append("--enable-mutation-testing")
    if getattr(args, "mutation_command_template", ""):
        cmd.extend(["--mutation-command-template", args.mutation_command_template])
    if getattr(args, "mutation_timeout", None) is not None:
        cmd.extend(["--mutation-timeout", str(args.mutation_timeout)])
    if getattr(args, "mutation_report_name", ""):
        cmd.extend(["--mutation-report-name", args.mutation_report_name])
    if args.fallback_model:
        cmd.extend(["--fallback-model", args.fallback_model])
    if args.fallback_temperature is not None:
        cmd.extend(["--fallback-temperature", str(args.fallback_temperature)])
    if args.openai_key:
        cmd.extend(["--openai-key", args.openai_key])

    return _run_cmd(cmd, cwd=root)


def _load_run(run_dir: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    metrics_path = run_dir / "metrics.json"
    pipeline_path = run_dir / "pipeline_results.json"
    if not metrics_path.exists():
        raise FileNotFoundError(f"Missing metrics file: {metrics_path}")
    if not pipeline_path.exists():
        raise FileNotFoundError(f"Missing pipeline results file: {pipeline_path}")
    return _read_json(metrics_path), _read_json(pipeline_path)


def _classification(results: list[dict[str, Any]]) -> dict[str, int]:
    counts = {
        "total": len(results),
        "compiled": 0,
        "verified": 0,
        "compiled_not_verified": 0,
        "non_compiling": 0,
        "zero_po_nonverified": 0,
        "near_miss_1_2": 0,
        "moderate_3_10": 0,
        "large_gt_10": 0,
    }
    for r in results:
        comp = bool(r.get("compiles"))
        ver = bool(r.get("verified"))
        po = int(r.get("proof_obligations", 0) or 0)
        un = int(r.get("unproven_obligations", 0) or 0)
        if comp:
            counts["compiled"] += 1
        else:
            counts["non_compiling"] += 1
        if ver:
            counts["verified"] += 1
        if comp and not ver:
            counts["compiled_not_verified"] += 1
            if po == 0:
                counts["zero_po_nonverified"] += 1
            elif un <= 2:
                counts["near_miss_1_2"] += 1
            elif un <= 10:
                counts["moderate_3_10"] += 1
            else:
                counts["large_gt_10"] += 1
    return counts


def _roundtrip_summary(results: list[dict[str, Any]]) -> dict[str, int]:
    counts = {
        "available": 0,
        "passed": 0,
        "failed": 0,
        "skipped": 0,
        "match": 0,
        "strict_match": 0,
        "exact_match": 0,
        "spec_equivalent": 0,
    }
    for r in results:
        rt = r.get("roundtrip") or {}
        if not isinstance(rt, dict):
            continue
        counts["available"] += 1
        status = rt.get("status", "skipped")
        if status == "passed":
            counts["passed"] += 1
        elif status == "failed":
            counts["failed"] += 1
        else:
            counts["skipped"] += 1
        if rt.get("roundtrip_match"):
            counts["match"] += 1
        if rt.get("strict_roundtrip_match"):
            counts["strict_match"] += 1
        if rt.get("exact_match"):
            counts["exact_match"] += 1
        if rt.get("spec_equivalent"):
            counts["spec_equivalent"] += 1
    return counts


def _svg_bars(title: str, labels: list[str], values: list[float], out_path: Path) -> None:
    width = 960
    height = 420
    margin_l = 80
    margin_r = 40
    margin_t = 60
    margin_b = 70
    plot_w = width - margin_l - margin_r
    plot_h = height - margin_t - margin_b
    n = max(1, len(values))
    max_v = max(values) if values else 1.0
    max_v = max(max_v, 1.0)
    gap = 14
    bar_w = (plot_w - gap * (n - 1)) / n

    lines: list[str] = []
    lines.append(f"<svg xmlns='http://www.w3.org/2000/svg' width='{width}' height='{height}' viewBox='0 0 {width} {height}'>")
    lines.append("<rect x='0' y='0' width='100%' height='100%' fill='white' />")
    lines.append(f"<text x='{margin_l}' y='32' font-size='22' font-family='Arial, Helvetica, sans-serif' fill='#111'>{title}</text>")
    lines.append(f"<line x1='{margin_l}' y1='{height - margin_b}' x2='{width - margin_r}' y2='{height - margin_b}' stroke='#333' stroke-width='1' />")
    lines.append(f"<line x1='{margin_l}' y1='{margin_t}' x2='{margin_l}' y2='{height - margin_b}' stroke='#333' stroke-width='1' />")

    for i, (label, value) in enumerate(zip(labels, values)):
        x = margin_l + i * (bar_w + gap)
        h = 0.0 if max_v <= 0 else (value / max_v) * plot_h
        y = margin_t + (plot_h - h)
        lines.append(f"<rect x='{x:.1f}' y='{y:.1f}' width='{bar_w:.1f}' height='{h:.1f}' fill='#4c78a8' />")
        lines.append(
            f"<text x='{x + bar_w / 2:.1f}' y='{height - margin_b + 18}' text-anchor='middle' font-size='12' font-family='Arial, Helvetica, sans-serif' fill='#222'>{label}</text>"
        )
        lines.append(
            f"<text x='{x + bar_w / 2:.1f}' y='{y - 6:.1f}' text-anchor='middle' font-size='12' font-family='Arial, Helvetica, sans-serif' fill='#111'>{value:.1f}</text>"
        )

    lines.append("</svg>")
    out_path.write_text("\n".join(lines), encoding="utf-8")


def command_summarize(args: argparse.Namespace) -> int:
    run_dir = Path(args.run_dir)
    out_dir = Path(args.out_dir)
    _ensure_dir(out_dir)

    metrics, pipeline = _load_run(run_dir)
    rows = list(pipeline.get("results", []))
    summary = metrics.get("summary", {})
    classes = _classification(rows)
    roundtrip = _roundtrip_summary(rows)

    durations = []
    for row in rows:
        trace = row.get("trace") or {}
        d = trace.get("duration_seconds")
        if isinstance(d, (int, float)):
            durations.append(float(d))

    derived = {
        "dataset": args.dataset,
        "run_dir": str(run_dir.resolve()),
        "total_files": classes["total"],
        "compiled_files": classes["compiled"],
        "verified_files": classes["verified"],
        "strict_success_rate_pct": _safe_pct(classes["verified"], classes["total"]),
        "compilation_rate_pct": _safe_pct(classes["compiled"], classes["total"]),
        "proof_obligations_total": int(summary.get("total_proof_obligations", 0) or 0),
        "proof_obligations_proven": int(summary.get("total_proven", 0) or 0),
        "proof_obligations_unproven": int(summary.get("total_unproven", 0) or 0),
        "proof_obligations_proven_pct": _safe_pct(
            int(summary.get("total_proven", 0) or 0),
            int(summary.get("total_proof_obligations", 0) or 0),
        ),
        "unproven_per_file": (
            (int(summary.get("total_unproven", 0) or 0) / classes["total"]) if classes["total"] else 0.0
        ),
        "tokens_in_total": int(pipeline.get("tokens_in_total", 0) or 0),
        "tokens_out_total": int(pipeline.get("tokens_out_total", 0) or 0),
        "api_cost_usd": float(summary.get("total_cost", pipeline.get("cost", 0.0)) or 0.0),
        "compiled_not_verified": classes["compiled_not_verified"],
        "zero_po_nonverified": classes["zero_po_nonverified"],
        "near_miss_1_2": classes["near_miss_1_2"],
        "moderate_3_10": classes["moderate_3_10"],
        "large_gt_10": classes["large_gt_10"],
        "roundtrip_available": roundtrip["available"],
        "roundtrip_passed": roundtrip["passed"],
        "roundtrip_failed": roundtrip["failed"],
        "roundtrip_skipped": roundtrip["skipped"],
        "roundtrip_match": roundtrip["match"],
        "roundtrip_strict_match": roundtrip["strict_match"],
        "roundtrip_exact_match": roundtrip["exact_match"],
        "roundtrip_spec_equivalent": roundtrip["spec_equivalent"],
        "duration_seconds_avg": statistics.mean(durations) if durations else 0.0,
        "duration_seconds_median": statistics.median(durations) if durations else 0.0,
    }

    (out_dir / "summary.json").write_text(json.dumps(derived, indent=2), encoding="utf-8")

    md_lines = [
        f"# formalspecc summary: {args.dataset}",
        "",
        "## Core outcomes",
        f"- Strict successful translations: {derived['verified_files']}/{derived['total_files']} ({derived['strict_success_rate_pct']:.1f}%)",
        f"- Compilation success: {derived['compiled_files']}/{derived['total_files']} ({derived['compilation_rate_pct']:.1f}%)",
        f"- Verification conditions closed: {derived['proof_obligations_proven']}/{derived['proof_obligations_total']} ({derived['proof_obligations_proven_pct']:.1f}%)",
        f"- Open conditions per file: {derived['unproven_per_file']:.2f}",
        "",
        "## Failure profile (compiled but not verified)",
        f"- Total compiled non-verified: {derived['compiled_not_verified']}",
        f"- Zero-obligation verifier aborts: {derived['zero_po_nonverified']}",
        f"- Near misses (1-2 unproved): {derived['near_miss_1_2']}",
        f"- Moderate gaps (3-10 unproved): {derived['moderate_3_10']}",
        f"- Large gaps (>10 unproved): {derived['large_gt_10']}",
        "",
        "## Round-trip back-translation",
        f"- Round-trip checks executed: {derived['roundtrip_available']}",
        f"- Round-trip passed: {derived['roundtrip_passed']}",
        f"- Round-trip failed: {derived['roundtrip_failed']}",
        f"- Round-trip skipped: {derived['roundtrip_skipped']}",
        f"- Round-trip matches: {derived['roundtrip_match']}",
        f"- Strict round-trip matches: {derived['roundtrip_strict_match']}",
        f"- Exact round-trip matches: {derived['roundtrip_exact_match']}",
        f"- Signature-equivalent round-trips: {derived['roundtrip_spec_equivalent']}",
        "",
        "## Cost and timing",
        f"- Input tokens: {derived['tokens_in_total']}",
        f"- Output tokens: {derived['tokens_out_total']}",
        f"- API cost (USD): {derived['api_cost_usd']:.2f}",
        f"- Avg file duration (s): {derived['duration_seconds_avg']:.2f}",
        f"- Median file duration (s): {derived['duration_seconds_median']:.2f}",
        "",
        "## Paper snippet",
        "```text",
        (
            f"Successful translations: {derived['verified_files']}/{derived['total_files']} | "
            f"Verified under WPRTE: {derived['strict_success_rate_pct']:.1f}% | "
            f"Verification conditions closed: {derived['proof_obligations_proven_pct']:.1f}% | "
            f"Open/file: {derived['unproven_per_file']:.2f}"
        ),
        "```",
    ]
    (out_dir / "summary.md").write_text("\n".join(md_lines), encoding="utf-8")

    print(f"Wrote summary files to: {out_dir}")
    return 0


def command_figures(args: argparse.Namespace) -> int:
    summary_path = Path(args.summary_json)
    out_dir = Path(args.out_dir)
    _ensure_dir(out_dir)
    s = _read_json(summary_path)

    _svg_bars(
        "Compile / verify",
        ["Total", "Compile", "Verify", "Open"],
        [
            float(s.get("total_files", 0)),
            float(s.get("compiled_files", 0)),
            float(s.get("verified_files", 0)),
            float(s.get("compiled_not_verified", 0)),
        ],
        out_dir / "status_counts.svg",
    )

    _svg_bars(
        "Verification gaps",
        ["Open", "1-2", "3-10", ">10"],
        [
            float(s.get("zero_po_nonverified", 0)),
            float(s.get("near_miss_1_2", 0)),
            float(s.get("moderate_3_10", 0)),
            float(s.get("large_gt_10", 0)),
        ],
        out_dir / "proof_gap_profile.svg",
    )

    print(f"Wrote figures to: {out_dir}")
    return 0


def command_all(args: argparse.Namespace) -> int:
    out_dir = Path(args.out_dir)
    _ensure_dir(out_dir)
    summary_dir = out_dir / "summary"
    figures_dir = out_dir / "figures"
    _ensure_dir(summary_dir)
    _ensure_dir(figures_dir)

    s_args = argparse.Namespace(dataset=args.dataset, run_dir=args.run_dir, out_dir=str(summary_dir))
    rc = command_summarize(s_args)
    if rc != 0:
        return rc
    f_args = argparse.Namespace(summary_json=str(summary_dir / "summary.json"), out_dir=str(figures_dir))
    return command_figures(f_args)


def command_roundtrip(args: argparse.Namespace) -> int:
    summary = compare_directories(
        original_dir=args.original_dir,
        roundtrip_dir=args.roundtrip_dir,
        dafny_executable=args.dafny_executable,
        out_dir=args.out_dir,
        generate_tests_mode=args.generate_tests_mode,
        test_backend=args.test_backend,
        timeout=args.timeout,
    )
    print(f"Dafny verify on both sides: {summary.get('verified_both', 0)}/{summary['total']}")
    print(f"Behavioral test-case match: {summary.get('output_match', 0)}/{summary['total']}")
    print(f"Exact text match: {summary.get('exact_match', 0)}/{summary['total']}")
    print(f"Summary written to: {Path(args.out_dir).resolve()}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="formalspecc project skill utilities")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_run = sub.add_parser("run", help="Run formalspecc pipeline")
    p_run.add_argument("--dataset", required=True, help="Input folder name under input/")
    p_run.add_argument("--output-root", default="runs", help="Output root folder")
    p_run.add_argument("--output-folder", default="", help="Optional run folder name under output root")
    p_run.add_argument("--model", default="gpt-5.2", help="Model name")
    p_run.add_argument("--temperature", type=float, default=0.2, help="Model temperature")
    p_run.add_argument("--checkpoint-every", type=int, default=10, help="Checkpoint interval")
    p_run.add_argument("--max-verify-iters", type=int, default=3, help="Max verification-improvement iterations")
    p_run.add_argument("--fallback-model", default="", help="Fallback model")
    p_run.add_argument("--fallback-temperature", type=float, default=None, help="Fallback temperature")
    p_run.add_argument("--skip-verification", action="store_true", help="Skip Frama-C verification")
    p_run.add_argument("--enable-differential-testing", dest="enable_differential_testing", action="store_true", help="Enable Dafny-to-C behavioral validation")
    p_run.add_argument("--skip-differential-testing", dest="enable_differential_testing", action="store_false", help="Skip Dafny-to-C behavioral validation")
    p_run.add_argument("--skip-roundtrip", action="store_true", help="Skip Dafny back-translation round-trip checking")
    p_run.add_argument("--dafny-executable", default="dafny", help="Dafny CLI executable or path")
    p_run.add_argument("--dafny-backend", default="cpp", help="Dafny backend used for behavioral validation builds")
    p_run.add_argument("--dafny-generate-tests-mode", default="InlinedBlock", help="Mode passed to 'dafny generate-tests'")
    p_run.add_argument("--dafny-test-backend", default="py", help="Backend used to execute generated Dafny tests")
    p_run.add_argument("--c-compiler", default="gcc", help="C compiler for generated validation harnesses")
    p_run.add_argument("--dtest-command-template", default="", help="Shell command template that writes test vectors to {vectors_file}")
    p_run.add_argument("--dafny-build-command-template", default="", help="Shell command template for building Dafny inputs")
    p_run.add_argument("--dafny-generated-tests-command-template", default="", help="Shell command template for running generated Dafny tests")
    p_run.add_argument("--translated-harness-dir", default="", help="Directory with pretranslated C test harnesses for end-to-end validation")
    p_run.add_argument("--enable-mutation-testing", dest="enable_mutation_testing", action="store_true", help="Enable mutation testing for translated ACSL outputs")
    p_run.add_argument("--skip-mutation-testing", dest="enable_mutation_testing", action="store_false", help="Skip mutation testing for translated ACSL outputs")
    p_run.add_argument("--mutation-command-template", default="", help="Shell command template for mutation testing")
    p_run.add_argument("--mutation-timeout", type=int, default=600, help="Timeout for mutation testing command")
    p_run.add_argument("--mutation-report-name", default="mutation_report.json", help="Mutation testing report filename")
    p_run.add_argument("--openai-key", default="", help="Optional API key override")
    p_run.set_defaults(enable_differential_testing=True, enable_mutation_testing=True)
    p_run.set_defaults(func=command_run)

    p_sum = sub.add_parser("summarize", help="Create summary files from run output")
    p_sum.add_argument("--dataset", required=True, help="Dataset label for summary headers")
    p_sum.add_argument("--run-dir", required=True, help="Path to a run directory (contains metrics.json)")
    p_sum.add_argument("--out-dir", default="analysis", help="Output directory for summary artifacts")
    p_sum.set_defaults(func=command_summarize)

    p_fig = sub.add_parser("figures", help="Create SVG figures from summary JSON")
    p_fig.add_argument("--summary-json", required=True, help="Path to summary.json")
    p_fig.add_argument("--out-dir", default="analysis/figures", help="Directory for SVG figures")
    p_fig.set_defaults(func=command_figures)

    p_all = sub.add_parser("all", help="Summarize and generate figures in one step")
    p_all.add_argument("--dataset", required=True, help="Dataset label for summary headers")
    p_all.add_argument("--run-dir", required=True, help="Path to run directory")
    p_all.add_argument("--out-dir", default="analysis", help="Base output directory")
    p_all.set_defaults(func=command_all)

    p_rt = sub.add_parser("roundtrip", help="Compare original and round-tripped Dafny directories")
    p_rt.add_argument("--original-dir", required=True, help="Directory with original Dafny files")
    p_rt.add_argument("--roundtrip-dir", required=True, help="Directory with round-tripped Dafny files")
    p_rt.add_argument("--out-dir", default="roundtrip-analysis", help="Directory for round-trip comparison outputs")
    p_rt.add_argument("--dafny-executable", default="dafny", help="Dafny CLI executable or path")
    p_rt.add_argument("--generate-tests-mode", default="InlinedBlock", help="Mode passed to dafny generate-tests")
    p_rt.add_argument("--test-backend", default="py", help="Backend passed to dafny test/run")
    p_rt.add_argument("--timeout", type=int, default=120, help="Timeout for Dafny commands in seconds")
    p_rt.set_defaults(func=command_roundtrip)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
