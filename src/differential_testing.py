"""Behavioral cross-check utilities for Dafny-to-C translation.

This module adds an optional validation stage that can:
1. Verify the Dafny source with the Dafny CLI.
2. Generate or load test vectors (either from a sidecar JSON file or an
   external DTest-style command).
3. Optionally build the Dafny program to a backend and run generated tests.
4. Compile and run a generated C harness against the translated C file.

The design is intentionally adapter-based because Dafny/DTest installations and
their invocation details vary significantly across environments.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import tempfile
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from .subprocess_creator import run_command, run_command_list


def _strip_acsl_comments(code: str) -> str:
    code = re.sub(r"/\*@.*?\*/", "", code, flags=re.DOTALL)
    code = re.sub(r"//@.*", "", code)
    return code


def _indent_block(text: str, prefix: str = "  ") -> str:
    return "\n".join(prefix + line if line.strip() else line for line in text.splitlines())


def _parse_primary_module_name(dafny_source: str) -> Optional[str]:
    match = re.search(r"^\s*module\s+([A-Za-z_][A-Za-z0-9_]*)", dafny_source, flags=re.MULTILINE)
    return match.group(1) if match else None


def _parse_dafny_literal(value: str) -> Any:
    text = value.strip()
    if text == "true":
        return True
    if text == "false":
        return False
    if text.startswith("[") and text.endswith("]"):
        inner = text[1:-1].strip()
        if not inner:
            return []
        return [_parse_dafny_literal(part) for part in _split_params(inner)]
    if re.fullmatch(r"-?\d+", text):
        return int(text)
    if text.startswith('"') and text.endswith('"'):
        return json.loads(text)
    raise ValueError(f"Unsupported Dafny literal: {value}")


def _json_type_for_value(value: Any) -> str:
    if isinstance(value, bool):
        return "bool"
    if isinstance(value, int):
        return "int"
    if isinstance(value, list) and all(isinstance(v, int) for v in value):
        return "seq<int>"
    if isinstance(value, str):
        return "string"
    return ""


def _format_dafny_literal(value: Any, type_name: str) -> str:
    normalized = " ".join(type_name.split())
    if normalized in {"int", "bool"}:
        return "true" if value is True else "false" if value is False else str(value)
    if normalized == "seq<int>":
        items = ", ".join(str(int(v)) for v in value)
        return f"[{items}]"
    raise ValueError(f"Unsupported Dafny type for runner literal: {type_name}")


def _split_params(params_raw: str) -> List[str]:
    params: List[str] = []
    depth = 0
    start = 0
    for idx, ch in enumerate(params_raw):
        if ch in "(<[":
            depth += 1
        elif ch in ")>]":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            params.append(params_raw[start:idx].strip())
            start = idx + 1
    tail = params_raw[start:].strip()
    if tail:
        params.append(tail)
    return params


def _parse_dafny_params(params_raw: str) -> List[Dict[str, str]]:
    params: List[Dict[str, str]] = []
    for raw in _split_params(params_raw):
        if ":" not in raw:
            return []
        name_part, type_part = raw.split(":", 1)
        type_name = type_part.strip()
        for name in [n.strip() for n in name_part.split(",") if n.strip()]:
            params.append({"name": name, "type": type_name})
    return params


def _extract_method_signatures(dafny_source: str) -> List[Dict[str, Any]]:
    pattern = re.compile(
        r"(?P<prefix>(?:\{:[^}]+\}\s*)*)method\s+(?P<inline_attrs>(?:\{:[^}]+\}\s*)*)(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\((?P<params>[^)]*)\)\s*(?:returns\s*\((?P<returns>[^)]*)\))?",
        re.MULTILINE,
    )
    methods: List[Dict[str, Any]] = []
    for match in pattern.finditer(dafny_source):
        prefix = (match.group("prefix") or "") + (match.group("inline_attrs") or "")
        methods.append(
            {
                "name": match.group("name"),
                "attrs": prefix,
                "params": _parse_dafny_params(match.group("params") or ""),
                "returns_raw": (match.group("returns") or "").strip(),
            }
        )
    return methods


def _extract_generated_test_cases(generated_tests_source: str) -> List[Dict[str, Any]]:
    method_pattern = re.compile(r"method\s+\{:\s*test\s*\}\s+(?P<name>\w+)\s*\(\)\s*\{(?P<body>.*?)\}", re.DOTALL)
    decl_pattern = re.compile(r"var\s+(?P<name>\w+)\s*:\s*(?P<type>[^:=]+?)\s*:=\s*(?P<value>.*?);")
    call_pattern = re.compile(r"(?:var\s+\w+\s*:=\s*)?(?P<call>[A-Za-z0-9_\.]+)\((?P<args>.*?)\);")
    cases: List[Dict[str, Any]] = []
    for match in method_pattern.finditer(generated_tests_source):
        name = match.group("name")
        body = match.group("body")
        env: Dict[str, Dict[str, Any]] = {}
        for decl in decl_pattern.finditer(body):
            env[decl.group("name")] = {
                "type": " ".join(decl.group("type").split()),
                "value": _parse_dafny_literal(decl.group("value")),
            }

        call_match = None
        for candidate in call_pattern.finditer(body):
            call_match = candidate
        if call_match is None:
            continue

        qualified = call_match.group("call")
        arg_texts = [a.strip() for a in _split_params(call_match.group("args")) if a.strip()]
        args: List[Any] = []
        arg_types: List[str] = []
        for arg in arg_texts:
            if arg in env:
                args.append(env[arg]["value"])
                arg_types.append(env[arg]["type"])
            else:
                args.append(_parse_dafny_literal(arg))
                arg_types.append("")
        cases.append({
            "name": name,
            "qualified_call": qualified,
            "function": qualified.split(".")[-1],
            "args": args,
            "arg_types": arg_types,
        })
    return cases


def _build_dafny_vector_runner(prepared_source_path: str, adapter_method: Dict[str, Any], cases: List[Dict[str, Any]]) -> str:
    include_path = prepared_source_path.replace("\\", "/")
    module_name = "FormalspeccGeneratedTests"
    adapter_name = adapter_method["name"]
    params = adapter_method.get("params", [])
    returns_raw = (adapter_method.get("returns_raw") or "").strip()
    if not returns_raw:
        raise ValueError("Vector runner currently requires a single return value")
    return_parts = _split_params(returns_raw)
    if len(return_parts) != 1 or ":" not in return_parts[0]:
        raise ValueError("Vector runner currently supports exactly one named return value")
    _, return_type = return_parts[0].split(":", 1)
    return_type = " ".join(return_type.split())
    if return_type not in {"int", "bool", "seq<int>"}:
        raise ValueError(f"Unsupported return type for vector extraction: {return_type}")

    lines = [
        f'include "{include_path}"',
        "module FormalspeccVectorRunner {",
        f"  import {module_name}",
        "  method Main() {",
    ]
    for idx, case in enumerate(cases):
        for p_idx, param in enumerate(params):
            lines.append(
                f"    var arg_{idx}_{p_idx}: {param['type']} := {_format_dafny_literal(case['args'][p_idx], param['type'])};"
            )
        call_args = ", ".join(f"arg_{idx}_{p_idx}" for p_idx, _ in enumerate(params))
        lines.append(f"    var result_{idx} := {module_name}.{adapter_name}({call_args});")
        lines.append(f"    print result_{idx}, \"\\n\";")
    lines.append("  }")
    lines.append("}")
    lines.append("")
    return "\n".join(lines)


def _supported_dafny_param_type(type_name: str) -> bool:
    t = " ".join(type_name.split())
    return t in {"int", "bool", "seq<int>", "array<int>"}


def _generate_dafny_test_adapter(module_name: str, method: Dict[str, Any]) -> Optional[str]:
    params = method.get("params", [])
    if not params:
        adapter_params = ""
        call_args = ""
        setup_lines: List[str] = []
    else:
        adapter_param_parts: List[str] = []
        call_args_list: List[str] = []
        setup_lines = []
        for param in params:
            p_name = param["name"]
            p_type = " ".join(param["type"].split())
            if not _supported_dafny_param_type(p_type):
                return None
            if p_type == "array<int>":
                adapter_param_parts.append(f"{p_name}: seq<int>")
                backing = f"{p_name}_array"
                setup_lines.append(f"var {backing} := new int[|{p_name}|];")
                setup_lines.append(f"for i := 0 to |{p_name}|")
                setup_lines.append("  invariant 0 <= i <= |%s|" % p_name)
                setup_lines.append("{")
                setup_lines.append(f"  {backing}[i] := {p_name}[i];")
                setup_lines.append("}")
                call_args_list.append(backing)
            else:
                adapter_param_parts.append(f"{p_name}: {p_type}")
                call_args_list.append(p_name)
        adapter_params = ", ".join(adapter_param_parts)
        call_args = ", ".join(call_args_list)

    adapter_name = f"FormalspeccTest_{method['name']}"
    returns_raw = method.get("returns_raw", "")
    returns_clause = f" returns ({returns_raw})" if returns_raw else ""
    invocation = f"{module_name}.{method['name']}({call_args})" if call_args else f"{module_name}.{method['name']}()"

    body_lines = setup_lines[:]
    if returns_raw:
        return_names = [part.split(":", 1)[0].strip() for part in _split_params(returns_raw)]
        if len(return_names) == 1:
            body_lines.append(f"{return_names[0]} := {invocation};")
        else:
            body_lines.append(f"var __formalspecc_result := {invocation};")
            for idx, return_name in enumerate(return_names):
                body_lines.append(f"{return_name} := __formalspecc_result.{idx};")
    else:
        body_lines.append(f"{invocation};")

    body = _indent_block("\n".join(body_lines), "  ") if body_lines else ""
    return (
        f"method {{:testEntry}} {adapter_name}({adapter_params}){returns_clause}\n"
        "{\n"
        f"{body}\n"
        "}"
    )


def _prepare_dafny_test_source(dafny_source: str, dafny_file: str, work_dir: str) -> Tuple[str, Dict[str, Any]]:
    module_name = _parse_primary_module_name(dafny_source)
    wrapped_source = dafny_source
    source_module = module_name or "FormalspeccSubject"
    if not module_name:
        wrapped_source = f"module {source_module} {{\n{_indent_block(dafny_source)}\n}}\n"

    methods = _extract_method_signatures(wrapped_source)
    adapters: List[str] = []
    adapter_infos: List[Dict[str, Any]] = []
    skipped_methods: List[str] = []
    for method in methods:
        adapter = _generate_dafny_test_adapter(source_module, method)
        if adapter:
            adapters.append(adapter)
            adapter_infos.append(
                {
                    "adapter_name": f"FormalspeccTest_{method['name']}",
                    "target_name": method["name"],
                    "params": method.get("params", []),
                    "returns_raw": method.get("returns_raw", ""),
                }
            )
        else:
            skipped_methods.append(method.get("name", "<unknown>"))

    if not adapters and "{:testEntry}" not in wrapped_source:
        raise ValueError("No supported methods available for generated {:testEntry} adapters")

    adapter_module = ""
    if adapters:
        adapters_joined = "\n\n".join(adapters)
        adapter_module = (
            f"\nmodule FormalspeccGeneratedTests {{\n"
            f"  import {source_module}\n\n"
            f"{_indent_block(adapters_joined)}\n"
            "}\n"
        )

    final_source = wrapped_source + adapter_module
    prepared_path = os.path.join(work_dir, os.path.basename(os.path.splitext(dafny_file)[0]) + ".prepared.dfy")
    with open(prepared_path, "w", encoding="utf-8") as f:
        f.write(final_source)
    return prepared_path, {
        "source_module": source_module,
        "generated_adapter_count": len(adapters),
        "generated_adapters": [info["adapter_name"] for info in adapter_infos],
        "adapter_infos": adapter_infos,
        "skipped_methods": skipped_methods,
        "prepared_source_path": os.path.abspath(prepared_path),
    }


def _find_adapter_method(prepared_source: str, adapter_name: str) -> Optional[Dict[str, Any]]:
    for method in _extract_method_signatures(prepared_source):
        if method.get("name") == adapter_name:
            return method
    return None


def _find_adapter_info(prepared_meta: Dict[str, Any], adapter_name: str) -> Optional[Dict[str, Any]]:
    for info in prepared_meta.get("adapter_infos", []):
        if info.get("adapter_name") == adapter_name:
            return info
    return None


def _parse_c_signature(c_code: str, function_name: str) -> Optional[Dict[str, Any]]:
    clean = _strip_acsl_comments(c_code)
    pattern = re.compile(
        rf"(?P<ret>[A-Za-z_][\w\s\*]*?)\s+{re.escape(function_name)}\s*\((?P<params>[^)]*)\)\s*\{{",
        re.MULTILINE,
    )
    match = pattern.search(clean)
    if not match:
        return None

    return_type = " ".join(match.group("ret").split())
    params_raw = match.group("params").strip()
    params: List[Dict[str, str]] = []
    if params_raw and params_raw != "void":
        for raw in params_raw.split(","):
            param = raw.strip()
            if not param:
                continue
            pieces = param.rsplit(" ", 1)
            if len(pieces) != 2:
                return None
            ptype = " ".join(pieces[0].split())
            pname = pieces[1].strip()
            if pname.startswith("*"):
                ptype = f"{ptype} *".strip()
                pname = pname.lstrip("*")
            params.append({"type": ptype, "name": pname})
    return {"return_type": return_type, "params": params}


def _normalize_type(type_name: str) -> str:
    normalized = " ".join(type_name.replace("const", "").split())
    normalized = normalized.replace(" *", "*")
    return normalized.strip()


def _c_literal(value: Any, type_name: str) -> str:
    t = _normalize_type(type_name)
    if t in {"int", "long", "short", "unsigned", "unsigned int", "size_t"}:
        return str(int(value))
    if t in {"bool", "_Bool"}:
        return "true" if bool(value) else "false"
    if t in {"double", "float"}:
        return repr(float(value))
    if t in {"char*", "char *", "const char*", "const char *"}:
        escaped = json.dumps(str(value))
        return escaped
    raise ValueError(f"Unsupported scalar C type: {type_name}")


def _supports_scalar_type(type_name: str) -> bool:
    t = _normalize_type(type_name)
    return t in {
        "int",
        "long",
        "short",
        "unsigned",
        "unsigned int",
        "size_t",
        "bool",
        "_Bool",
        "double",
        "float",
        "char*",
        "char *",
        "const char*",
        "const char *",
    }


def _supports_array_type(type_name: str) -> bool:
    t = _normalize_type(type_name)
    return t in {"int*", "int *", "const int*", "const int *"}


def _build_harness_source(
    translated_c_path: str,
    function_name: str,
    signature: Dict[str, Any],
    cases: List[Dict[str, Any]],
) -> str:
    vector_signature = signature.get("vector_signature") or {}
    ret_type = signature.get("return_type", "").strip()
    params = signature.get("params", [])
    ret_norm = _normalize_type(ret_type)
    vector_ret = " ".join((vector_signature.get("return_type") or "").split())

    sequence_result_pattern = False
    if vector_ret == "seq<int>":
        if len(params) in {5, 6}:
            p = [_normalize_type(param.get("type", "")) for param in params]
            sequence_result_pattern = (
                p[0] in {"int*", "const int*"}
                and p[1] in {"int", "size_t"}
                and p[2] in {"int*", "const int*"}
                and p[3] in {"int", "size_t"}
                and p[4] == "int*"
                and ret_norm in {"int", "size_t"}
                and (len(params) == 5 or p[5] in {"int", "size_t"})
            )

    if not sequence_result_pattern:
        if ret_norm == "void":
            raise ValueError("Void-returning functions are not supported by the generated harness")
        if not _supports_scalar_type(ret_norm):
            raise ValueError(f"Unsupported return type for generated harness: {ret_type}")

    lines = [
        "#include <stdbool.h>",
        "#include <stdio.h>",
        "#include <stdlib.h>",
        "#include <string.h>",
        f'#include "{os.path.basename(translated_c_path)}"',
        "",
        "static int failures = 0;",
        "",
    ]

    for idx, case in enumerate(cases):
        name = case.get("name") or f"case_{idx}"
        args = case.get("args", [])
        logical_seq_case = sequence_result_pattern and len(args) == 2
        if not logical_seq_case and len(args) != len(params):
            raise ValueError(f"Case '{name}' does not match parameter count")

        decls: List[str] = []
        call_args: List[str] = []
        if logical_seq_case:
            if not all(isinstance(arg, list) for arg in args):
                raise ValueError(f"Case '{name}' expected two sequence arguments")
            a_vals = ", ".join(str(int(v)) for v in args[0])
            b_vals = ", ".join(str(int(v)) for v in args[1])
            decls.append(f"int arg_{idx}_0[] = {{{a_vals}}};")
            decls.append(f"int arg_{idx}_1[] = {{{b_vals}}};")
            call_args = [f"arg_{idx}_0", str(len(args[0])), f"arg_{idx}_1", str(len(args[1]))]
        else:
            for param_idx, param in enumerate(params):
                ptype = param.get("type", "")
                pname = f"arg_{idx}_{param_idx}"
                value = args[param_idx]
                if _supports_array_type(ptype):
                    if not isinstance(value, list):
                        raise ValueError(f"Case '{name}' expected a list for parameter '{param.get('name', pname)}'")
                    values = ", ".join(str(int(v)) for v in value)
                    decls.append(f"int {pname}[] = {{{values}}};")
                    call_args.append(pname)
                elif _supports_scalar_type(ptype):
                    decls.append(f"{ptype} {pname} = {_c_literal(value, ptype)};")
                    call_args.append(pname)
                else:
                    raise ValueError(f"Unsupported parameter type for generated harness: {ptype}")

        lines.append(f"static void run_{idx}(void) {{")
        for decl in decls:
            lines.append(f"  {decl}")
        if sequence_result_pattern:
            expected = case.get("expected")
            if not isinstance(expected, list):
                raise ValueError(f"Case '{name}' expected sequence output")
            expected_vals = ", ".join(str(int(v)) for v in expected)
            cap = max(len(expected), len(case.get("args", [[], []])[0]) if case.get("args") else 0, 1)
            lines.append(f"  int expected[] = {{{expected_vals}}};")
            lines.append(f"  int actual_out[{cap}];")
            if len(params) == 6:
                lines.append(f"  {ret_type} actual_len = {function_name}({call_args[0]}, {call_args[1]}, {call_args[2]}, {call_args[3]}, actual_out, {cap});")
            else:
                lines.append(f"  {ret_type} actual_len = {function_name}({call_args[0]}, {call_args[1]}, {call_args[2]}, {call_args[3]}, actual_out);")
            lines.append(f"  if ((int)actual_len != {len(expected)}) {{")
            lines.append("    failures += 1;")
            lines.append(f'    fprintf(stderr, "[FAIL] {name}: length mismatch\\n");')
            lines.append("    return;")
            lines.append("  }")
            lines.append(f"  for (int i = 0; i < {len(expected)}; ++i) {{")
            lines.append("    if (actual_out[i] != expected[i]) {")
            lines.append("      failures += 1;")
            lines.append(f'      fprintf(stderr, "[FAIL] {name}: element mismatch at %d\\n", i);')
            lines.append("      return;")
            lines.append("    }")
            lines.append("  }")
        else:
            expected = _c_literal(case.get("expected"), ret_type)
            if ret_norm in {"char*", "char *", "const char*", "const char *"}:
                lines.append(f"  {ret_type} expected = {expected};")
            else:
                lines.append(f"  {ret_type} expected = ({ret_type})({expected});")
            lines.append(f"  {ret_type} actual = {function_name}({', '.join(call_args)});")
            if ret_norm in {"double", "float"}:
                comparison = f"(actual < expected ? expected - actual : actual - expected) > 1e-9"
            elif ret_norm in {"char*", "char *", "const char*", "const char *"}:
                comparison = "strcmp(actual, expected) != 0"
            else:
                comparison = "actual != expected"
            lines.append(f"  if ({comparison}) {{")
            lines.append("    failures += 1;")
            lines.append(f'    fprintf(stderr, "[FAIL] {name}\\n");')
            lines.append("  }")
        lines.append("}")
        lines.append("")

    lines.append("int main(void) {")
    for idx in range(len(cases)):
        lines.append(f"  run_{idx}();")
    lines.append("  if (failures) {")
    lines.append('    fprintf(stderr, "Harness failures: %d\\n", failures);')
    lines.append("    return 1;")
    lines.append("  }")
    lines.append('  printf("All harness cases passed\\n");')
    lines.append("  return 0;")
    lines.append("}")
    lines.append("")
    return "\n".join(lines)


@dataclass
class DifferentialTestingConfig:
    enabled: bool = False
    dafny_executable: str = "dafny"
    backend: str = "cpp"
    generate_tests_mode: str = "InlinedBlock"
    test_backend: str = "py"
    verify_timeout: int = 120
    dtest_timeout: int = 120
    build_timeout: int = 180
    run_timeout: int = 120
    c_compiler: str = "gcc"
    dtest_command_template: str = ""
    dafny_build_command_template: str = ""
    dafny_generated_tests_command_template: str = ""


class DifferentialTester:
    def __init__(self, config: DifferentialTestingConfig):
        self.config = config

    def _run_list(self, args: List[str], timeout: int) -> Dict[str, Any]:
        stdout, stderr, success = run_command_list(args, timeout=timeout)
        return {
            "success": success,
            "stdout": stdout,
            "stderr": stderr,
            "command": args,
        }

    def _run_template(self, template: str, context: Dict[str, Any], timeout: int) -> Dict[str, Any]:
        command = template.format(**context)
        stdout, stderr, success = run_command(command, timeout=timeout, shell=True)
        return {
            "success": success,
            "stdout": stdout,
            "stderr": stderr,
            "command": command,
        }

    def _dafny_available(self) -> bool:
        if os.path.isfile(self.config.dafny_executable):
            return True
        return bool(shutil.which(self.config.dafny_executable))

    def _compiler_available(self) -> bool:
        if os.path.isfile(self.config.c_compiler):
            return True
        return bool(shutil.which(self.config.c_compiler))

    def _sidecar_vectors_path(self, dafny_file: str) -> str:
        return f"{os.path.splitext(dafny_file)[0]}.tests.json"

    def _load_vectors(self, vectors_path: str) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
        if not os.path.exists(vectors_path):
            return None, f"Missing test vector file: {vectors_path}"
        try:
            with open(vectors_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as err:
            return None, f"Failed to parse test vectors: {err}"
        return data, None

    def run(self, dafny_file: str, dafny_source: str, translated_c_path: str, translated_c_code: str, work_dir: str) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "enabled": self.config.enabled,
            "dafny_verify": {"status": "skipped", "reason": "disabled"},
            "test_vectors": {"status": "skipped", "reason": "disabled"},
            "dafny_build": {"status": "skipped", "reason": "disabled"},
            "dafny_generated_tests": {"status": "skipped", "reason": "disabled"},
            "c_harness": {"status": "skipped", "reason": "disabled"},
            "overall_passed": False,
        }
        if not self.config.enabled:
            return result

        os.makedirs(work_dir, exist_ok=True)
        result["work_dir"] = os.path.abspath(work_dir)
        result["translated_c_path"] = os.path.abspath(translated_c_path)

        try:
            prepared_dafny_file, prepared_meta = _prepare_dafny_test_source(dafny_source, dafny_file, work_dir)
            result["prepared_dafny"] = prepared_meta
        except Exception as err:
            result["prepared_dafny"] = {"status": "failed", "reason": str(err)}
            return result

        if self._dafny_available():
            verify_res = self._run_list(
                [self.config.dafny_executable, "verify", prepared_dafny_file],
                timeout=self.config.verify_timeout,
            )
            verify_res["status"] = "passed" if verify_res["success"] else "failed"
            result["dafny_verify"] = verify_res
        else:
            result["dafny_verify"] = {"status": "skipped", "reason": f"Command not found: {self.config.dafny_executable}"}

        vectors_path = os.path.join(work_dir, "generated.tests.json")
        sidecar_path = self._sidecar_vectors_path(dafny_file)
        if self.config.dtest_command_template:
            context = {
                "dafny_file": os.path.abspath(dafny_file),
                "work_dir": os.path.abspath(work_dir),
                "vectors_file": os.path.abspath(vectors_path),
                "backend": self.config.backend,
            }
            dtest_res = self._run_template(self.config.dtest_command_template, context, timeout=self.config.dtest_timeout)
            dtest_res["status"] = "passed" if dtest_res["success"] and os.path.exists(vectors_path) else "failed"
            if dtest_res["status"] == "failed" and not os.path.exists(vectors_path):
                dtest_res["stderr"] = (dtest_res.get("stderr", "") + "\nNo vectors file produced").strip()
            result["test_vectors"] = dtest_res
        elif os.path.exists(sidecar_path):
            shutil.copyfile(sidecar_path, vectors_path)
            result["test_vectors"] = {
                "status": "passed",
                "source": os.path.abspath(sidecar_path),
                "vectors_file": os.path.abspath(vectors_path),
            }
        else:
            result["test_vectors"] = {
                "status": "skipped",
                "reason": "No DTest command template configured and no sidecar .tests.json file found",
                "expected_sidecar": os.path.abspath(sidecar_path),
            }

        if self._dafny_available():
            if self.config.dafny_build_command_template:
                context = {
                    "dafny_file": os.path.abspath(prepared_dafny_file),
                    "work_dir": os.path.abspath(work_dir),
                    "backend": self.config.backend,
                }
                build_res = self._run_template(self.config.dafny_build_command_template, context, timeout=self.config.build_timeout)
            else:
                build_res = self._run_list(
                    [self.config.dafny_executable, "build", f"--target:{self.config.backend}", prepared_dafny_file],
                    timeout=self.config.build_timeout,
                )
            build_res["status"] = "passed" if build_res["success"] else "failed"
            result["dafny_build"] = build_res
        else:
            result["dafny_build"] = {"status": "skipped", "reason": f"Command not found: {self.config.dafny_executable}"}

        if self.config.dafny_generated_tests_command_template:
            context = {
                "dafny_file": os.path.abspath(dafny_file),
                "work_dir": os.path.abspath(work_dir),
                "vectors_file": os.path.abspath(vectors_path),
                "backend": self.config.backend,
            }
            generated_tests_res = self._run_template(
                self.config.dafny_generated_tests_command_template,
                context,
                timeout=self.config.run_timeout,
            )
            generated_tests_res["status"] = "passed" if generated_tests_res["success"] else "failed"
            result["dafny_generated_tests"] = generated_tests_res
        elif self._dafny_available():
            generated_tests_res = self._run_list(
                [
                    self.config.dafny_executable,
                    "generate-tests",
                    self.config.generate_tests_mode,
                    prepared_dafny_file,
                ],
                timeout=self.config.run_timeout,
            )
            generated_tests_output = os.path.join(work_dir, "dafny_generate_tests_output.txt")
            with open(generated_tests_output, "w", encoding="utf-8") as f:
                f.write((generated_tests_res.get("stdout", "") or "") + "\n" + (generated_tests_res.get("stderr", "") or ""))
            generated_tests_file = os.path.join(work_dir, "generated_tests.dfy")
            if generated_tests_res.get("success") and (generated_tests_res.get("stdout") or "").strip():
                with open(generated_tests_file, "w", encoding="utf-8") as f:
                    f.write(generated_tests_res.get("stdout", ""))
                generated_cases = _extract_generated_test_cases(generated_tests_res.get("stdout", ""))
                test_run_res = self._run_list(
                    [
                        self.config.dafny_executable,
                        "test",
                        generated_tests_file,
                        "--target",
                        self.config.test_backend,
                    ],
                    timeout=self.config.run_timeout,
                )
                generated_tests_res["test_run"] = test_run_res
                generated_tests_res["generated_tests_file"] = os.path.abspath(generated_tests_file)
                generated_tests_res["generated_case_count"] = len(generated_cases)
                if generated_cases:
                    with open(prepared_dafny_file, "r", encoding="utf-8") as f:
                        prepared_source_text = f.read()
                    adapter_method = _find_adapter_method(prepared_source_text, generated_cases[0]["function"])
                    if adapter_method:
                        try:
                            runner_source = _build_dafny_vector_runner(prepared_dafny_file, adapter_method, generated_cases)
                            runner_file = os.path.join(work_dir, "vector_runner.dfy")
                            with open(runner_file, "w", encoding="utf-8") as f:
                                f.write(runner_source)
                            runner_res = self._run_list(
                                [
                                    self.config.dafny_executable,
                                    "run",
                                    runner_file,
                                    "--target",
                                    self.config.test_backend,
                                ],
                                timeout=self.config.run_timeout,
                            )
                            generated_tests_res["vector_runner"] = runner_res
                            generated_tests_res["vector_runner_file"] = os.path.abspath(runner_file)
                            if runner_res.get("success"):
                                stdout_lines = [line.strip() for line in (runner_res.get("stdout", "") or "").splitlines() if line.strip()]
                                output_lines = stdout_lines[-len(generated_cases):] if generated_cases else []
                                vectors_cases = []
                                for case, output_line in zip(generated_cases, output_lines):
                                    vectors_cases.append({
                                        "name": case["name"],
                                        "args": case["args"],
                                        "expected": _parse_dafny_literal(output_line),
                                    })
                                adapter_info = _find_adapter_info(prepared_meta, adapter_method["name"])
                                target_name = adapter_info.get("target_name") if adapter_info else adapter_method["name"]
                                vectors_signature = {
                                    "return_type": return_type,
                                    "params": [{"name": p["name"], "type": p["type"]} for p in adapter_method.get("params", [])],
                                } if (return_type := " ".join(_split_params(adapter_method.get("returns_raw", ""))[0].split(":", 1)[1].split())) else None
                                vectors_payload = {
                                    "function": target_name,
                                    "signature": vectors_signature,
                                    "cases": vectors_cases,
                                }
                                with open(vectors_path, "w", encoding="utf-8") as f:
                                    json.dump(vectors_payload, f, indent=2)
                                generated_tests_res["vectors_file"] = os.path.abspath(vectors_path)
                                result["test_vectors"] = {
                                    "status": "passed",
                                    "source": "dafny-generated-tests",
                                    "vectors_file": os.path.abspath(vectors_path),
                                    "case_count": len(vectors_cases),
                                }
                        except Exception as err:
                            generated_tests_res["vector_runner"] = {"success": False, "stderr": str(err)}
                generated_tests_res["status"] = "passed" if test_run_res.get("success") else "failed"
            else:
                generated_tests_res["status"] = "failed"
            generated_tests_res["output_file"] = os.path.abspath(generated_tests_output)
            result["dafny_generated_tests"] = generated_tests_res
        else:
            result["dafny_generated_tests"] = {
                "status": "skipped",
                "reason": "No Dafny generated-tests command template configured and Dafny CLI is unavailable",
            }

        vectors, vector_error = self._load_vectors(vectors_path) if os.path.exists(vectors_path) else (None, None)
        if vector_error:
            result["c_harness"] = {"status": "failed", "reason": vector_error}
            return result
        if not vectors:
            result["c_harness"] = {
                "status": "skipped",
                "reason": "No test vectors available for harness generation",
            }
            return result

        if not self._compiler_available():
            result["c_harness"] = {
                "status": "skipped",
                "reason": f"Command not found: {self.config.c_compiler}",
            }
            return result

        function_name = vectors.get("function")
        if not function_name:
            result["c_harness"] = {"status": "failed", "reason": "Vector file must define a 'function' field"}
            return result

        signature = _parse_c_signature(translated_c_code, function_name)
        if not signature:
            result["c_harness"] = {
                "status": "failed",
                "reason": f"Unable to infer C signature for function '{function_name}'",
            }
            return result
        signature["vector_signature"] = vectors.get("signature") or {}

        cases = vectors.get("cases") or []
        if not cases:
            result["c_harness"] = {"status": "failed", "reason": "Vector file has no test cases"}
            return result

        harness_dir = os.path.join(work_dir, "c_harness")
        os.makedirs(harness_dir, exist_ok=True)
        translated_copy = os.path.join(harness_dir, os.path.basename(translated_c_path))
        if os.path.abspath(translated_copy) != os.path.abspath(translated_c_path):
            shutil.copyfile(translated_c_path, translated_copy)

        try:
            harness_source = _build_harness_source(translated_copy, function_name, signature, cases)
        except Exception as err:
            result["c_harness"] = {"status": "failed", "reason": str(err)}
            return result

        harness_path = os.path.join(harness_dir, "generated_harness.c")
        with open(harness_path, "w", encoding="utf-8") as f:
            f.write(harness_source)

        exe_name = "generated_harness.exe" if os.name == "nt" else "generated_harness"
        exe_path = os.path.join(harness_dir, exe_name)
        compile_res = self._run_list(
            [self.config.c_compiler, harness_path, "-std=c11", "-o", exe_path],
            timeout=self.config.run_timeout,
        )
        if not compile_res["success"]:
            compile_res["status"] = "failed"
            compile_res["harness_path"] = os.path.abspath(harness_path)
            result["c_harness"] = compile_res
            return result

        run_res = self._run_list([exe_path], timeout=self.config.run_timeout)
        run_res["status"] = "passed" if run_res["success"] else "failed"
        run_res["harness_path"] = os.path.abspath(harness_path)
        run_res["executable_path"] = os.path.abspath(exe_path)
        run_res["signature"] = signature
        run_res["case_count"] = len(cases)
        result["c_harness"] = run_res

        result["backend_build_passed"] = result["dafny_build"].get("status") in {"passed", "skipped"}
        result["overall_passed"] = (
            result["c_harness"].get("status") == "passed"
            and result["dafny_verify"].get("status") in {"passed", "skipped"}
            and result["test_vectors"].get("status") in {"passed", "skipped"}
            and result["dafny_generated_tests"].get("status") in {"passed", "skipped"}
        )
        return result
