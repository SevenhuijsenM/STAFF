"""ACSL Pipeline - Core pipeline implementation."""

import os
import re
import time
import sys
import json
import platform
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Dict, Any, Optional
from openai import OpenAI

from .metrics import MetricsCalculator
from .mutation_testing import MutationTester, MutationTestingConfig
from .verify import verify_with_wp, compile_c, verify_dafny, compile_dafny
from .subprocess_creator import run_command_list
from .differential_testing import DifferentialTester, DifferentialTestingConfig
from prompts import generate_initial_prompt, generate_improvement_prompt_compilation, generate_improvement_prompt_verification


def extract_dafny_stats(code: str) -> Dict:
    """Extract stats from Dafny code."""
    return {
        "requires": len(re.findall(r'\brequires\b', code)),
        "ensures": len(re.findall(r'\bensures\b', code)),
        "invariant": len(re.findall(r'\binvariant\b', code)),
        "decreases": len(re.findall(r'\bdecreases\b', code)),
        "modifies": len(re.findall(r'\bmodifies\b', code)),
    }


class LLMClient:
    """Handles all LLM interactions."""
    
    def __init__(self, api_key: str, model: str, temperature: float, source_lang: str = "dafny"):
        self.client = OpenAI(api_key=api_key)
        self.model = model
        self.temperature = temperature
        self.source_lang = source_lang
    
    def _params(self) -> Dict[str, Any]:
        if "gpt-5" in self.model.lower() or "o1" in self.model.lower() or "o3" in self.model.lower():
            return {"max_completion_tokens": 8000}
        return {"max_tokens": 4000}

    @staticmethod
    def _sanitize_text(text: str) -> str:
        if not text:
            return text
        cleaned = []
        for ch in text:
            if ch in ("\n", "\r", "\t"):
                cleaned.append(ch)
                continue
            if ord(ch) < 32:
                cleaned.append(" ")
            else:
                cleaned.append(ch)
        return "".join(cleaned)
    
    def _call(self, prompt: str, system: str):
        prompt_clean = prompt
        system_clean = system
        last_err = None
        started = time.time()
        for attempt in range(3):
            try:
                resp = self.client.chat.completions.create(
                    model=self.model,
                    messages=[{"role": "system", "content": system_clean}, {"role": "user", "content": prompt_clean}],
                    temperature=self.temperature, **self._params()
                )
                return resp, (time.time() - started), (attempt + 1)
            except Exception as err:
                last_err = err
                msg = str(err)
                if "parse the JSON body" in msg and attempt == 0:
                    prompt_clean = self._sanitize_text(prompt_clean)
                    system_clean = self._sanitize_text(system_clean)
                    continue
                if attempt < 2:
                    time.sleep(1.5 * (attempt + 1))
                    continue
        raise last_err
    
    @staticmethod
    def _response_text(resp) -> str:
        msg = resp.choices[0].message.content
        return msg if msg else ""

    def translate(self, code: str, target_lang: str = "ACSL") -> Dict[str, Any]:
        prompt = generate_initial_prompt(code, self.source_lang, target_lang)
        system = f"You are an expert in translating {self.source_lang} to {target_lang}."
        try:
            resp, latency, attempts = self._call(prompt, system)
            return {
                "code": self._extract(resp),
                "usage": resp.usage,
                "prompt": prompt,
                "system": system,
                "raw_response": self._response_text(resp),
                "latency_seconds": latency,
                "attempts": attempts,
                "error": "",
            }
        except Exception as err:
            return {
                "code": None,
                "usage": None,
                "prompt": prompt,
                "system": system,
                "raw_response": "",
                "latency_seconds": None,
                "attempts": 3,
                "error": str(err),
            }
    
    def fix(self, source_code: str, current_translation: str, error: str, target_lang: str = "ACSL") -> Dict[str, Any]:
        prompt = generate_improvement_prompt_compilation(source_code, current_translation, error, self.source_lang, target_lang)
        system = "You are an expert in formal specification translation and verification."
        try:
            resp, latency, attempts = self._call(prompt, system)
            return {
                "code": self._extract(resp),
                "usage": resp.usage,
                "prompt": prompt,
                "system": system,
                "raw_response": self._response_text(resp),
                "latency_seconds": latency,
                "attempts": attempts,
                "error": "",
            }
        except Exception as err:
            return {
                "code": None,
                "usage": None,
                "prompt": prompt,
                "system": system,
                "raw_response": "",
                "latency_seconds": None,
                "attempts": 3,
                "error": str(err),
            }
    
    def improve(self, source_code: str, current_translation: str, verif: Dict, target_lang: str = "ACSL") -> Dict[str, Any]:
        fb = self._fmt_verif(verif)
        prompt = generate_improvement_prompt_verification(source_code, current_translation, fb, self.source_lang, target_lang)
        system = "You are an expert in formal specification translation and verification."
        try:
            resp, latency, attempts = self._call(prompt, system)
            return {
                "code": self._extract(resp),
                "usage": resp.usage,
                "prompt": prompt,
                "system": system,
                "raw_response": self._response_text(resp),
                "latency_seconds": latency,
                "attempts": attempts,
                "error": "",
            }
        except Exception as err:
            return {
                "code": None,
                "usage": None,
                "prompt": prompt,
                "system": system,
                "raw_response": "",
                "latency_seconds": None,
                "attempts": 3,
                "error": str(err),
            }
    
    def _fmt_verif(self, v: Dict) -> str:
        if not v: return "No verification results."
        return f"Proof obligations: {v.get('proof_obligations', 0)}, Proven: {v.get('proven_obligations', 0)}, Unproven: {v.get('unproven_obligations', 0)}"
    
    def _extract(self, resp) -> Optional[str]:
        text = resp.choices[0].message.content.strip() if resp.choices[0].message.content else ""
        if not text:
            print("Warning: No code found.")
            return None
        patterns = [
            r"<dafny_code>(.*?)</dafny_code>",
            r"<_?c_code_with_acsl>(.*?)</c_code_with_acsl>",
            r"<code>(.*?)</code>",
            r"<c_code>(.*?)</c_code>",
            r"<acsl_code>(.*?)</acsl_code>",
            r"```dafny\n?(.*?)```",
            r"```c\n?(.*?)```",
            r"```\n?(.*?)```",
        ]
        for pat in patterns:
            if m := re.search(pat, text, re.DOTALL):
                return m.group(1).strip().strip('`').strip()
        print("Warning: No code found.")
        return None


class ACSLPipeline:
    PRICE_PER_1K = 0.01

    def __init__(self, model: str = "gpt-5.2", temperature: float = 0.7, source_lang: str = "dafny",
                 input_dir: str = "input", output_dir: str = "output", skip_verif: bool = False,
                 api_key: str = "", debug: bool = False, fallback_model: Optional[str] = None,
                 fallback_temperature: Optional[float] = None, checkpoint_every: int = 0,
                 resume: bool = False, max_verify_iters: int = 3,
                 differential_testing: Optional[DifferentialTestingConfig] = None,
                 mutation_testing: Optional[MutationTestingConfig] = None,
                 roundtrip_enabled: bool = True,
                 target_lang: str = "ACSL", dafny_executable: str = "dafny",
                 translated_harness_dir: Optional[str] = None):
        self.model = model
        self.temperature = temperature
        self.source_lang = source_lang
        self.input_dir = input_dir
        self.output_dir = output_dir
        self.skip_verif = skip_verif
        self.debug = debug
        self.fallback_model = fallback_model
        self.fallback_temperature = temperature if fallback_temperature is None else fallback_temperature
        self.checkpoint_every = max(0, int(checkpoint_every or 0))
        self.resume = resume
        self.max_verify_iters = max(0, int(max_verify_iters or 0))
        self.roundtrip_enabled = bool(roundtrip_enabled)
        self.target_lang = target_lang
        self.dafny_executable = dafny_executable
        self.translated_harness_dir = translated_harness_dir or ""
        
        self.llm = LLMClient(api_key, model, temperature, source_lang)
        self.llm_fallback = LLMClient(api_key, fallback_model, self.fallback_temperature, source_lang) if fallback_model else None
        self.roundtrip_llm = LLMClient(api_key, model, temperature, "acsl")
        self.results: List[Dict] = []
        self.tokens_in = self.tokens_out = 0
        self.metrics = MetricsCalculator()
        self.start_time = None
        self.total = self.done = 0
        self.run_started_at = datetime.now(timezone.utc).isoformat()
        self.run_finished_at = ""
        self.differential_testing = differential_testing or DifferentialTestingConfig(enabled=False)
        self.differential_tester = DifferentialTester(self.differential_testing)
        self.mutation_testing = mutation_testing or MutationTestingConfig(enabled=False)
        self.mutation_tester = MutationTester(self.mutation_testing)
        self.translated_harness_validation_reports: List[Dict[str, Any]] = []

    def _run_translated_harness_validation(self, out_folder: str) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "enabled": bool(self.translated_harness_dir),
            "status": "skipped",
            "reason": "disabled" if not self.translated_harness_dir else "not run",
        }
        if not self.translated_harness_dir:
            return result

        harness_dir = Path(self.translated_harness_dir)
        if not harness_dir.exists():
            result["reason"] = f"Harness directory not found: {harness_dir}"
            return result

        validator = Path(__file__).resolve().parent.parent / "validate_translated_harnesses.py"
        report_path = Path(out_folder) / "translated_harness_validation_report.json"
        work_dir = Path(out_folder) / "translated_harness_validation_work"
        cmd = [
            sys.executable,
            str(validator),
            "--harness-dir",
            str(harness_dir.resolve()),
            "--solution-dir",
            str(Path(out_folder).resolve()),
            "--compiler",
            self.differential_testing.c_compiler,
            "--report",
            str(report_path.resolve()),
            "--work-dir",
            str(work_dir.resolve()),
        ]
        stdout, stderr, success = run_command_list(cmd, timeout=7200)
        result.update({
            "command": cmd,
            "stdout": stdout,
            "stderr": stderr,
            "success": success,
            "harness_dir": str(harness_dir.resolve()),
            "solution_dir": str(Path(out_folder).resolve()),
            "report_file": str(report_path.resolve()),
            "work_dir": str(work_dir.resolve()),
        })
        if report_path.exists():
            try:
                report = json.loads(report_path.read_text(encoding="utf-8"))
            except Exception as err:
                result["status"] = "failed"
                result["report_error"] = str(err)
                return result
            result["report"] = report
            result["passed"] = int(report.get("passed", 0) or 0)
            result["failed"] = int(report.get("failed", 0) or 0)
            result["skipped"] = int(report.get("skipped", 0) or 0)
            result["total"] = int(report.get("total", 0) or 0)
            result["status"] = "passed" if result["failed"] == 0 else "failed"
            result["reason"] = "completed"
        elif not success:
            result["status"] = "failed"
            result["reason"] = "validator did not produce a report"
        return result

    def _run_roundtrip_check(self, original_path: str, original_source: str, translated_code: str, work_dir: str, base: str, trace: Dict[str, Any]) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "enabled": self.roundtrip_enabled,
            "status": "skipped",
            "reason": "disabled" if not self.roundtrip_enabled else "not applicable",
        }
        if not self.roundtrip_enabled:
            return result
        if self.source_lang.lower() != "dafny" or self.target_lang.lower() != "acsl":
            result["reason"] = "round-trip comparison is only enabled for forward Dafny->ACSL runs"
            return result
        if not translated_code:
            result["reason"] = "Missing translated ACSL-annotated C code"
            return result

        roundtrip_dir = os.path.join(work_dir, "roundtrip", base)
        os.makedirs(roundtrip_dir, exist_ok=True)
        roundtrip_path = os.path.join(roundtrip_dir, f"{base}.roundtrip.dfy")

        call_started_at = datetime.now(timezone.utc).isoformat()
        llm_res = self.roundtrip_llm.translate(translated_code, "dafny")
        call_completed_at = datetime.now(timezone.utc).isoformat()
        roundtrip_call = {
            "stage": "roundtrip_translation",
            "model": self.model,
            "source_lang": "acsl",
            "target_lang": "dafny",
            "started_at": call_started_at,
            "completed_at": call_completed_at,
            "latency_seconds": llm_res.get("latency_seconds"),
            "attempts": llm_res.get("attempts", 0),
            "error": llm_res.get("error", ""),
            "prompt": llm_res.get("prompt", ""),
            "system": llm_res.get("system", ""),
            "raw_response": llm_res.get("raw_response", ""),
            "extracted_code": llm_res.get("code") or "",
            "tokens_in": llm_res.get("usage").prompt_tokens if llm_res.get("usage") else 0,
            "tokens_out": llm_res.get("usage").completion_tokens if llm_res.get("usage") else 0,
        }
        trace.setdefault("llm_calls", []).append(roundtrip_call)

        if not llm_res.get("code"):
            result.update({
                "status": "failed",
                "reason": llm_res.get("error") or "No round-trip Dafny code generated",
                "translation": roundtrip_call,
            })
            return result

        os.makedirs(roundtrip_dir, exist_ok=True)
        with open(roundtrip_path, "w", encoding="utf-8") as f:
            f.write(llm_res.get("code") or "")

        from .roundtrip import compare_dafny_roundtrip

        try:
            compare = compare_dafny_roundtrip(
                original_file=original_path,
                roundtrip_file=roundtrip_path,
                dafny_executable=self.dafny_executable,
                generate_tests_mode=self.differential_testing.generate_tests_mode,
                test_backend=self.differential_testing.test_backend,
                timeout=self.differential_testing.verify_timeout,
            )
            result.update({
                "status": "passed",
                "reason": "",
                "translation": roundtrip_call,
                "roundtrip_file": os.path.abspath(roundtrip_path),
                "comparison": compare,
                "roundtrip_match": bool(compare.get("roundtrip_match")),
                "strict_roundtrip_match": bool(compare.get("strict_roundtrip_match")),
                "exact_match": bool(compare.get("exact_match")),
                "normalized_text_match": bool(compare.get("normalized_text_match")),
                "spec_equivalent": bool(compare.get("spec_equivalent")),
            })
        except Exception as err:
            result.update({
                "status": "failed",
                "reason": str(err),
                "translation": roundtrip_call,
                "roundtrip_file": os.path.abspath(roundtrip_path),
            })
        return result

    @staticmethod
    def _natural_key(name: str):
        parts = re.split(r"(\d+)", name)
        return [int(p) if p.isdigit() else p.lower() for p in parts]

    @classmethod
    def _file_sort_key(cls, filename: str):
        if m := re.search(r'task_id_(\d+)', filename):
            return (0, int(m.group(1)), filename.lower())
        return (1, cls._natural_key(filename))

    def _debug(self, *a, **kw):
        if self.debug:
            print("\n" + "="*50)
            print("DEBUG:", *a, **kw)
            print("="*50)

    def _progress(self):
        if not self.total: return
        elapsed = time.time() - (self.start_time or time.time())
        avg = elapsed / max(self.done, 1)
        eta = avg * (self.total - self.done)
        m, s = int(eta//60), int(eta%60)
        p = self.done / self.total
        bar = "#" * int(30 * p) + "-" * (30 - int(30 * p))
        sys.stdout.write(f"\r[{bar}] {self.done}/{self.total} ({p*100:.1f}%) ETA:{m}m {s}s")
        sys.stdout.flush()

    def process_file(self, path: str, out_folder: str) -> Dict:
        fname = os.path.basename(path)
        base = os.path.splitext(fname)[0]
        file_started = time.time()
        file_started_at = datetime.now(timezone.utc).isoformat()

        def _now_iso() -> str:
            return datetime.now(timezone.utc).isoformat()

        trace: Dict[str, Any] = {
            "filename": fname,
            "started_at": file_started_at,
            "llm_calls": [],
            "compile_attempts": [],
            "verification_runs": [],
            "behavioral_validation": {},
            "roundtrip": {},
            "mutation_testing": {},
            "structural_fidelity": {},
            "notes": [],
        }

        def _token_totals() -> tuple[int, int]:
            tin = sum(int(c.get("tokens_in", 0) or 0) for c in trace["llm_calls"])
            tout = sum(int(c.get("tokens_out", 0) or 0) for c in trace["llm_calls"])
            return tin, tout
        
        with open(path) as f:
            src = f.read()
        
        # Extract Dafny stats
        dafny_stats = extract_dafny_stats(src)
        
        # Translate (with optional fallback model for untranslated files)
        call_started_at = _now_iso()
        res = self.llm.translate(src, self.target_lang)
        call_completed_at = _now_iso()
        trace["llm_calls"].append({
            "stage": "initial_translation",
            "model": self.model,
            "started_at": call_started_at,
            "completed_at": call_completed_at,
            "latency_seconds": res.get("latency_seconds"),
            "attempts": res.get("attempts", 0),
            "error": res.get("error", ""),
            "prompt": res.get("prompt", ""),
            "system": res.get("system", ""),
            "raw_response": res.get("raw_response", ""),
            "extracted_code": res.get("code") or "",
            "tokens_in": res.get("usage").prompt_tokens if res.get("usage") else 0,
            "tokens_out": res.get("usage").completion_tokens if res.get("usage") else 0,
        })
        code = res.get("code", "")
        translation_model = self.model
        fallback_used = False

        if not code and self.llm_fallback:
            self._debug(f"Retrying translation with fallback model for {fname}")
            call_started_at = _now_iso()
            res_fb = self.llm_fallback.translate(src)
            call_completed_at = _now_iso()
            trace["llm_calls"].append({
                "stage": "fallback_translation",
                "model": self.fallback_model,
                "started_at": call_started_at,
                "completed_at": call_completed_at,
                "latency_seconds": res_fb.get("latency_seconds"),
                "attempts": res_fb.get("attempts", 0),
                "error": res_fb.get("error", ""),
                "prompt": res_fb.get("prompt", ""),
                "system": res_fb.get("system", ""),
                "raw_response": res_fb.get("raw_response", ""),
                "extracted_code": res_fb.get("code") or "",
                "tokens_in": res_fb.get("usage").prompt_tokens if res_fb.get("usage") else 0,
                "tokens_out": res_fb.get("usage").completion_tokens if res_fb.get("usage") else 0,
            })
            code = res_fb.get("code", "")
            translation_model = self.fallback_model or self.model
            fallback_used = True

        if not code and not (res.get("error") or "").strip():
            print(f"  ! {base} empty output from {translation_model} during initial translation")
        
        self._debug(f"Translated {fname}", code[:200] if code else "None")
        
        if not code:
            trace["notes"].append("No translatable code extracted from LLM responses")
            trace["completed_at"] = _now_iso()
            trace["duration_seconds"] = time.time() - file_started
            token_in_total, token_out_total = _token_totals()
            return {
                "filename": fname,
                "error": res.get("error") or "No code generated",
                "translated": False,
                "translation_model": translation_model,
                "fallback_used": fallback_used,
                "tokens_in": token_in_total,
                "tokens_out": token_out_total,
                "dafny_stats": dafny_stats,
                "trace": trace,
            }
        
        # Fix compilation (max 3)
        fix_attempts = 0
        for att in range(3):
            compile_started = time.time()
            ok, err = compile_c(c_code=code)
            trace["compile_attempts"].append({
                "stage": "initial_fix_loop",
                "attempt": att + 1,
                "success": ok,
                "error": err,
                "duration_seconds": time.time() - compile_started,
                "timestamp": _now_iso(),
            })
            if not ok and code:
                fix_attempts += 1
                call_started_at = _now_iso()
                fix_res = self.llm.fix(src, code, err, self.target_lang)
                call_completed_at = _now_iso()
                trace["llm_calls"].append({
                    "stage": "fix_compilation",
                    "model": self.model,
                    "started_at": call_started_at,
                    "completed_at": call_completed_at,
                    "latency_seconds": fix_res.get("latency_seconds"),
                    "attempts": fix_res.get("attempts", 0),
                    "error": fix_res.get("error", ""),
                    "prompt": fix_res.get("prompt", ""),
                    "system": fix_res.get("system", ""),
                    "raw_response": fix_res.get("raw_response", ""),
                    "extracted_code": fix_res.get("code") or "",
                    "tokens_in": fix_res.get("usage").prompt_tokens if fix_res.get("usage") else 0,
                    "tokens_out": fix_res.get("usage").completion_tokens if fix_res.get("usage") else 0,
                })
                code = fix_res.get("code") or ""
                if not code:
                    trace["notes"].append("Compilation fix stage returned no code")
                    print(f"  ! {base} empty output from {self.model} during compile-fix attempt {att + 1}")
                    break
            else:
                break
        
        compiles = False
        verified = False
        proof_obls = 0
        proven = 0
        unproven = 0
        verify_repair_attempts = 0
        final = code or ""
        current_code = code or ""
        verif: Dict[str, Any] = {}

        if current_code:
            compile_started = time.time()
            if self.target_lang.lower() == "dafny":
                compiles, compile_err = compile_dafny(dafny_code=current_code, dafny_executable=self.dafny_executable)
            else:
                compiles, compile_err = compile_c(c_code=current_code)
            trace["compile_attempts"].append({
                "stage": "post_fix_baseline",
                "attempt": 1,
                "success": compiles,
                "error": compile_err,
                "duration_seconds": time.time() - compile_started,
                "timestamp": _now_iso(),
            })
            if compiles and not self.skip_verif:
                if self.target_lang.lower() == "dafny":
                    verif = verify_dafny(dafny_code=current_code, dafny_executable=self.dafny_executable)
                else:
                    verif = verify_with_wp(c_code=current_code)
                trace["verification_runs"].append({
                    "stage": "post_fix_baseline",
                    "timestamp": _now_iso(),
                    **verif,
                })
                verified = verif.get("verified", False)
                proof_obls = verif.get("proof_obligations", 0)
                proven = verif.get("proven_obligations", 0)
                unproven = verif.get("unproven_obligations", 0)
                if verified:
                    print(f"  · {base} baseline verify passed ({proven}/{proof_obls})")
                elif proof_obls == 0:
                    print(f"  · {base} baseline verifier abort (0 proof obligations formed)")
                else:
                    print(f"  · {base} baseline verify incomplete ({proven}/{proof_obls}, unproved={unproven})")
            elif not compiles:
                short_err = (compile_err or "").strip().splitlines()[0] if compile_err else "compile failed"
                print(f"  · {base} baseline compile failed: {short_err}")

        if current_code and self.max_verify_iters > 0 and not self.skip_verif:
            for iter_idx in range(1, self.max_verify_iters + 1):
                if compiles and verified:
                    break

                verify_repair_attempts += 1
                call_started_at = _now_iso()
                improve_res = self.llm.improve(src, current_code, verif, self.target_lang)
                call_completed_at = _now_iso()
                trace["llm_calls"].append({
                    "stage": "improve_verification",
                    "iteration": iter_idx,
                    "model": self.model,
                    "started_at": call_started_at,
                    "completed_at": call_completed_at,
                    "latency_seconds": improve_res.get("latency_seconds"),
                    "attempts": improve_res.get("attempts", 0),
                    "error": improve_res.get("error", ""),
                    "prompt": improve_res.get("prompt", ""),
                    "system": improve_res.get("system", ""),
                    "raw_response": improve_res.get("raw_response", ""),
                    "extracted_code": improve_res.get("code") or "",
                    "tokens_in": improve_res.get("usage").prompt_tokens if improve_res.get("usage") else 0,
                    "tokens_out": improve_res.get("usage").completion_tokens if improve_res.get("usage") else 0,
                })

                improved = improve_res.get("code") or ""
                if not improved:
                    trace["notes"].append(f"Verify-improve iteration {iter_idx} returned no code")
                    print(f"  ! {base} empty output from {self.model} during verify-repair iteration {iter_idx}")
                    continue

                compile_started = time.time()
                if self.target_lang.lower() == "dafny":
                    improved_compiles, improved_compile_err = compile_dafny(dafny_code=improved, dafny_executable=self.dafny_executable)
                else:
                    improved_compiles, improved_compile_err = compile_c(c_code=improved)
                trace["compile_attempts"].append({
                    "stage": "improved_candidate",
                    "iteration": iter_idx,
                    "attempt": 1,
                    "success": improved_compiles,
                    "error": improved_compile_err,
                    "duration_seconds": time.time() - compile_started,
                    "timestamp": _now_iso(),
                })

                if not improved_compiles:
                    trace["notes"].append(f"Verify-improve iteration {iter_idx} produced non-compiling code")
                    short_err = (improved_compile_err or "").strip().splitlines()[0] if improved_compile_err else "compile failed"
                    print(f"  · {base} verify-repair iteration {iter_idx} compile failed: {short_err}")
                    continue

                if self.target_lang.lower() == "dafny":
                    v_iter = verify_dafny(dafny_code=improved, dafny_executable=self.dafny_executable)
                else:
                    v_iter = verify_with_wp(c_code=improved)
                trace["verification_runs"].append({
                    "stage": "improved_candidate",
                    "iteration": iter_idx,
                    "timestamp": _now_iso(),
                    **v_iter,
                })

                current_code = improved
                final = improved
                compiles = True
                verif = v_iter
                verified = v_iter.get("verified", False)
                proof_obls = v_iter.get("proof_obligations", 0)
                proven = v_iter.get("proven_obligations", 0)
                unproven = v_iter.get("unproven_obligations", 0)

                if verified:
                    print(f"  · {base} verify-repair iteration {iter_idx} passed ({proven}/{proof_obls})")
                elif proof_obls == 0:
                    print(f"  · {base} verify-repair iteration {iter_idx} verifier abort (0 proof obligations formed)")
                else:
                    print(f"  · {base} verify-repair iteration {iter_idx} incomplete ({proven}/{proof_obls}, unproved={unproven})")

                if verified:
                    break
        
        # Determine folder
        target = out_folder
        if not compiles:
            target = os.path.join(out_folder, "non_compiling")
        elif not verified:
            target = os.path.join(out_folder, "non_verifying")
        
        os.makedirs(target, exist_ok=True)
        
        # Save initial in separate folder
        initial_folder = os.path.join(out_folder, "initial")
        os.makedirs(initial_folder, exist_ok=True)
        target_ext = ".dfy" if self.target_lang.lower() == "dafny" else ".c"
        initial_path = os.path.join(initial_folder, f"{base}_initial{target_ext}")
        with open(initial_path, 'w', encoding="utf-8") as f:
            f.write(code)
        
        final_path = os.path.join(target, f"{base}{target_ext}")
        with open(final_path, 'w', encoding="utf-8") as f:
            f.write(final or "")
        target_spec_stats = self.metrics.count_specifications(final or "")
        structural_fidelity = {
            "source": {
                "requires": dafny_stats.get("requires", 0),
                "ensures": dafny_stats.get("ensures", 0),
                "invariant": dafny_stats.get("invariant", 0),
                "modifies": dafny_stats.get("modifies", 0),
            },
            "target": {
                "requires": target_spec_stats.get("requires", 0),
                "ensures": target_spec_stats.get("ensures", 0),
                "invariant": target_spec_stats.get("loop_invariant", 0),
                "assigns": target_spec_stats.get("assigns", 0),
            },
            "preservation": {},
        }
        for key, target_key in [("requires", "requires"), ("ensures", "ensures"), ("invariant", "invariant"), ("modifies", "assigns")]:
            source_value = structural_fidelity["source"].get(key, 0)
            target_value = structural_fidelity["target"].get(target_key, 0)
            structural_fidelity["preservation"][key] = {
                "source_count": source_value,
                "target_count": target_value,
                "presence_preserved": source_value > 0 and target_value > 0,
                "count_exact_match": source_value == target_value,
                "count_ratio": (min(source_value, target_value) / source_value) if source_value else None,
                "overgeneration_ratio": (target_value / source_value) if source_value else None,
            }
        trace["structural_fidelity"] = structural_fidelity

        validation_dir = os.path.join(out_folder, "behavioral_validation", base)
        validation_result = self.differential_tester.run(
            dafny_file=path,
            dafny_source=src,
            translated_c_path=final_path,
            translated_c_code=final or "",
            work_dir=validation_dir,
        )
        trace["behavioral_validation"] = validation_result
        if self.differential_testing.enabled:
            validation_status = validation_result.get("c_harness", {}).get("status", "skipped")
            overall_status = "passed" if validation_result.get("overall_passed") else validation_status
            print(f"  · {base} behavioral validation {overall_status}")

        mutation_dir = os.path.join(out_folder, "mutation_testing", base)
        mutation_result = {
            "enabled": self.mutation_testing.enabled,
            "status": "skipped",
            "reason": "disabled" if not self.mutation_testing.enabled else "not run",
        }
        if self.target_lang.lower() != "dafny":
            mutation_result = self.mutation_tester.run(
                translated_c_path=final_path,
                translated_c_code=final or "",
                work_dir=mutation_dir,
                source_file=path,
                source_code=src,
            )
            if self.mutation_testing.enabled:
                print(f"  Â· {base} mutation testing {mutation_result.get('status', 'skipped')}")
        trace["mutation_testing"] = mutation_result

        roundtrip_dir = os.path.join(out_folder, "roundtrip", base)
        roundtrip_result = self._run_roundtrip_check(path, src, final or "", roundtrip_dir, base, trace)
        trace["roundtrip"] = roundtrip_result
        if self.roundtrip_enabled:
            if roundtrip_result.get("status") == "passed":
                print(f"  · {base} round-trip check passed")
            else:
                print(f"  · {base} round-trip check {roundtrip_result.get('status', 'skipped')}")

        trace_dir = os.path.join(out_folder, "traces")
        os.makedirs(trace_dir, exist_ok=True)
        trace["artifacts"] = {
            "initial_code_path": os.path.abspath(initial_path),
            "final_code_path": os.path.abspath(final_path),
            "roundtrip_code_path": os.path.abspath(roundtrip_result.get("roundtrip_file", "")) if roundtrip_result.get("roundtrip_file") else "",
            "trace_path": os.path.abspath(os.path.join(trace_dir, f"{base}.trace.json")),
        }
        trace["completed_at"] = _now_iso()
        trace["duration_seconds"] = time.time() - file_started
        with open(trace["artifacts"]["trace_path"], "w", encoding="utf-8") as f:
            json.dump(trace, f, indent=2)
        
        # Status: V = verified, ~ = compiles, X = failed
        status = "V" if (compiles and verified) else ("~" if compiles else "X")

        repair_parts = []
        if fix_attempts:
            repair_parts.append(f"{fix_attempts} compile-fix")
        if verify_repair_attempts:
            repair_parts.append(f"{verify_repair_attempts} verify-repair")
        repair_info = f" ({', '.join(repair_parts)})" if repair_parts else ""
        outcome_info = ""
        if compiles:
            outcome_info = f" [po={proof_obls}, proved={proven}, unproved={unproven}]"
        print(f"  {status} {base}{repair_info}{outcome_info}")
        token_in_total, token_out_total = _token_totals()
        
        return {
            "filename": fname, "source": src, "final": final,
            "compiles": compiles, "verified": verified,
            "proof_obligations": proof_obls,
            "proven_obligations": proven,
            "unproven_obligations": unproven,
            "tokens_in": token_in_total,
            "tokens_out": token_out_total,
            "dafny_stats": dafny_stats,
            "translated": True,
            "translation_model": translation_model,
            "fallback_used": fallback_used,
            "behavioral_validation": validation_result,
            "roundtrip": roundtrip_result,
            "mutation_testing": mutation_result,
            "structural_fidelity": structural_fidelity,
            "trace": trace,
        }

    def process_folder(self, name: str, output_name: str | None = None):
        inp = os.path.join(self.input_dir, name)
        out_name = output_name or name
        out = os.path.join(self.output_dir, out_name)
        os.makedirs(out, exist_ok=True)
        
        if not os.path.exists(inp):
            print(f"Input not found: {inp}")
            return
        
        expected_ext = '.c' if self.source_lang.lower() == 'acsl' else '.dfy'
        files_all = sorted([f for f in os.listdir(inp) if f.endswith(expected_ext)], key=self._file_sort_key)
        files = files_all

        if self.resume:
            processed = set()
            for sub in ["", "non_verifying", "non_compiling"]:
                p = os.path.join(out, sub)
                if os.path.isdir(p):
                    for cfile in os.listdir(p):
                        if cfile.endswith(".c"):
                            processed.add(os.path.splitext(cfile)[0])
            files = [f for f in files_all if os.path.splitext(f)[0] not in processed]
            print(f"\n=== {out_name} ({len(files)} pending / {len(files_all)} total, resume mode) ===")
        else:
            print(f"\n=== {out_name} ({len(files)} files) ===")
        
        self.start_time = time.time()
        self.total = len(files)
        self.done = 0
        
        try:
            for i, f in enumerate(files):
                try:
                    r = self.process_file(os.path.join(inp, f), out)
                except Exception as err:
                    base = os.path.splitext(f)[0]
                    print(f"\n  ! {base} error: {err}")
                    r = {
                        "filename": f,
                        "error": str(err),
                        "translated": False,
                        "tokens_in": 0,
                        "tokens_out": 0,
                        "compiles": False,
                        "verified": False,
                        "trace": {
                            "filename": f,
                            "started_at": datetime.now(timezone.utc).isoformat(),
                            "completed_at": datetime.now(timezone.utc).isoformat(),
                            "duration_seconds": 0.0,
                            "error": str(err),
                        },
                    }
                self.results.append(r)
                self.tokens_in += r.get("tokens_in", 0)
                self.tokens_out += r.get("tokens_out", 0)
                self.done += 1
                self._progress()
                
                self.metrics.evaluate_translation(
                    r.get("source", ""), r.get("final", ""),
                    r.get("tokens_in", 0), r.get("tokens_out", 0),
                    r.get("filename", ""), self.source_lang, self.target_lang,
                    pre_compiled=r.get("compiles"),
                    pre_verified=r.get("verified"),
                    pre_proof_obligations=r.get("proof_obligations"),
                    pre_proven=r.get("proven_obligations"),
                    pre_unproven=r.get("unproven_obligations"),
                    dafny_stats=r.get("dafny_stats"),
                    src_code=r.get("source", ""),
                    tgt_code=r.get("final", ""),
                )

                if self.checkpoint_every > 0 and self.done % self.checkpoint_every == 0:
                    self.save(out_name)
                    print(f"\n  [checkpoint] saved progress at {self.done}/{self.total}")
        except KeyboardInterrupt:
            print("\nInterrupted. Saving checkpoint before exit...")
            self.save(out_name)
            raise

        if files:
            print()

        harness_validation_result = self._run_translated_harness_validation(out)
        if self.translated_harness_dir:
            if harness_validation_result.get("status") == "passed":
                print(f"  · {out_name} translated-harness validation passed")
            else:
                print(f"  · {out_name} translated-harness validation {harness_validation_result.get('status', 'skipped')}")
        self.translated_harness_validation_reports.append({
            "folder": out_name,
            **harness_validation_result,
        })
        
        elapsed = time.time() - self.start_time
        print(f"  Done in {elapsed/60:.1f}m")
        
        # Count stats
        compiled = sum(1 for r in self.results if r.get("compiles"))
        verified = sum(1 for r in self.results if r.get("verified"))
        print(f"  V{verified}  ~{compiled-verified}  X{len(files)-compiled}")

    def save(self, name: str = None):
        out = os.path.join(self.output_dir, name) if name else self.output_dir
        os.makedirs(out, exist_ok=True)
        
        untranslated = [r.get("filename") for r in self.results if not r.get("translated", True)]
        roundtrip_rows = [r.get("roundtrip") for r in self.results if isinstance(r.get("roundtrip"), dict)]
        harness_validation_rows = list(getattr(self, "translated_harness_validation_reports", []))
        roundtrip_summary = {
            "available": len(roundtrip_rows),
            "passed": sum(1 for r in roundtrip_rows if r.get("status") == "passed"),
            "failed": sum(1 for r in roundtrip_rows if r.get("status") == "failed"),
            "skipped": sum(1 for r in roundtrip_rows if r.get("status") == "skipped"),
            "matched": sum(1 for r in roundtrip_rows if r.get("roundtrip_match")),
            "strict_matched": sum(1 for r in roundtrip_rows if r.get("strict_roundtrip_match")),
            "exact_match": sum(1 for r in roundtrip_rows if r.get("exact_match")),
            "spec_equivalent": sum(1 for r in roundtrip_rows if r.get("spec_equivalent")),
        }
        harness_validation_summary = {
            "available": len(harness_validation_rows),
            "passed": sum(1 for r in harness_validation_rows if r.get("status") == "passed"),
            "failed": sum(1 for r in harness_validation_rows if r.get("status") == "failed"),
            "skipped": sum(1 for r in harness_validation_rows if r.get("status") == "skipped"),
        }

        summary = {
            "config": {
                "model": self.model,
                "temp": self.temperature,
                "lang": self.source_lang,
                "skip_verification": self.skip_verif,
                "fallback_model": self.fallback_model,
                "fallback_temperature": self.fallback_temperature,
                "checkpoint_every": self.checkpoint_every,
                "resume": self.resume,
                "roundtrip_enabled": self.roundtrip_enabled,
                "translated_harness_dir": self.translated_harness_dir,
                "differential_testing": {
                    "enabled": self.differential_testing.enabled,
                    "dafny_executable": self.differential_testing.dafny_executable,
                    "backend": self.differential_testing.backend,
                    "generate_tests_mode": self.differential_testing.generate_tests_mode,
                    "test_backend": self.differential_testing.test_backend,
                    "c_compiler": self.differential_testing.c_compiler,
                    "dtest_command_template": self.differential_testing.dtest_command_template,
                    "dafny_build_command_template": self.differential_testing.dafny_build_command_template,
                    "dafny_generated_tests_command_template": self.differential_testing.dafny_generated_tests_command_template,
                },
            },
            "run": {
                "started_at": self.run_started_at,
                "finished_at": self.run_finished_at or datetime.now(timezone.utc).isoformat(),
                "saved_at": datetime.now(timezone.utc).isoformat(),
                "platform": platform.platform(),
                "python": sys.version,
                "hostname": platform.node(),
            },
            "results": self.results,
            "cost": (self.tokens_in + self.tokens_out) / 1000 * self.PRICE_PER_1K,
            "tokens_in_total": self.tokens_in,
            "tokens_out_total": self.tokens_out,
            "untranslated_count": len(untranslated),
            "untranslated_files": untranslated,
            "roundtrip": roundtrip_summary,
            "translated_harness_validation": harness_validation_summary,
        }
        
        with open(os.path.join(out, "pipeline_results.json"), 'w', encoding="utf-8") as f:
            json.dump(summary, f, indent=2)

        with open(os.path.join(out, "pipeline_results.jsonl"), 'w', encoding="utf-8") as f:
            for row in self.results:
                f.write(json.dumps(row) + "\n")

        with open(os.path.join(out, "untranslated_files.txt"), 'w', encoding="utf-8") as f:
            for fname in untranslated:
                f.write(f"{fname}\n")
        
        self.metrics.save_results(os.path.join(out, "metrics.json"))

    def run(self, folders: List[str] = None):
        print(f"\nformalspecc - {self.model} (temp={self.temperature})")
        self.run_started_at = datetime.now(timezone.utc).isoformat()
        
        if not folders and os.path.exists(self.input_dir):
            folders = sorted([d for d in os.listdir(self.input_dir) if os.path.isdir(os.path.join(self.input_dir, d))])
        
        for f in (folders or []):
            if isinstance(f, (tuple, list)) and len(f) == 2:
                input_name, output_name = f[0], f[1]
            else:
                input_name, output_name = f, f
            self.process_folder(input_name, output_name)
            self.save(output_name)

        self.run_finished_at = datetime.now(timezone.utc).isoformat()
        self.save()
        
        stats = self.metrics.get_summary()
        print(f"\n=== Complete ===")
        print(f"Processed: {stats.get('total_programs', 0)}")
        print(f"Compiled: {stats.get('compilation_success_rate', 0)*100:.1f}%")
        print(f"Verified: {stats.get('verification_success_rate', 0)*100:.1f}%")
        print(f"Cost: ${stats.get('total_cost', 0):.2f}")
