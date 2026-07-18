"""Optional mutation-testing hook for translated ACSL artifacts."""

from __future__ import annotations

import json
import os
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional

from .subprocess_creator import run_command


@dataclass
class MutationTestingConfig:
    enabled: bool = False
    command_template: str = ""
    timeout: int = 600
    report_name: str = "mutation_report.json"


class MutationTester:
    def __init__(self, config: MutationTestingConfig):
        self.config = config

    def _run_template(self, template: str, context: Dict[str, Any], timeout: int) -> Dict[str, Any]:
        command = template.format(**context)
        stdout, stderr, success = run_command(command, timeout=timeout, shell=True)
        return {
            "success": success,
            "stdout": stdout,
            "stderr": stderr,
            "command": command,
        }

    def run(
        self,
        *,
        translated_c_path: str,
        translated_c_code: str,
        work_dir: str,
        source_file: str = "",
        source_code: str = "",
    ) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "enabled": self.config.enabled,
            "status": "skipped",
            "reason": "disabled" if not self.config.enabled else "not configured",
        }
        if not self.config.enabled:
            return result
        if not self.config.command_template.strip():
            result["reason"] = "No mutation command template configured"
            return result
        if not translated_c_path or not os.path.exists(translated_c_path):
            result["status"] = "failed"
            result["reason"] = "Missing translated C artifact"
            return result

        os.makedirs(work_dir, exist_ok=True)
        report_file = os.path.join(work_dir, self.config.report_name)
        context = {
            "translated_c_path": os.path.abspath(translated_c_path),
            "translated_c_code": translated_c_code,
            "translated_c_filename": Path(translated_c_path).name,
            "source_file": os.path.abspath(source_file) if source_file else "",
            "source_code": source_code,
            "work_dir": os.path.abspath(work_dir),
            "report_file": os.path.abspath(report_file),
        }

        run_res = self._run_template(self.config.command_template, context, timeout=self.config.timeout)
        result.update(run_res)
        result["status"] = "passed" if run_res.get("success") else "failed"
        result["report_file"] = os.path.abspath(report_file)

        if os.path.exists(report_file):
            try:
                with open(report_file, "r", encoding="utf-8") as f:
                    result["report"] = json.load(f)
            except Exception as err:
                result["report_parse_error"] = str(err)
        return result
