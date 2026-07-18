"""Translate Dafny test cases to plain C using OpenAI or OpenRouter."""

import argparse
import json
import os
import re
import sys
import time
from fnmatch import fnmatch
from pathlib import Path
from typing import Iterable, List

from openai import OpenAI

sys.path.insert(0, str(Path(__file__).resolve().parent))

from src.config import Config


DEFAULT_MODEL = "gpt-5.4-mini"
DEFAULT_PROVIDER = "openai"
OPENROUTER_BASE_URL = "https://openrouter.ai/api/v1"
API_KEY_PLACEHOLDER_MARKERS = (
    "your_key",
    "your-api-key",
    "your_api_key",
    "replace_with",
    "sk-...",
    "<your",
)


def looks_like_placeholder_api_key(value: str) -> bool:
    normalized = (value or "").strip().lower()
    return bool(normalized) and any(marker in normalized for marker in API_KEY_PLACEHOLDER_MARKERS)


def collect_input_files(root: Path, recursive: bool, patterns: Iterable[str]) -> List[Path]:
    files: List[Path] = []
    if recursive:
        candidates = [p for p in root.rglob("*") if p.is_file()]
    else:
        candidates = [p for p in root.iterdir() if p.is_file()]

    for path in candidates:
        if any(fnmatch(path.name, pattern) for pattern in patterns):
            files.append(path)
    return sorted(files)


def create_client(provider: str, api_key: str) -> OpenAI:
    provider_name = (provider or DEFAULT_PROVIDER).strip().lower()
    if provider_name == "openrouter":
        return OpenAI(api_key=api_key, base_url=OPENROUTER_BASE_URL)
    return OpenAI(api_key=api_key)


def load_signature_map(signature_map_path: str | None) -> str:
    if not signature_map_path:
        return ""
    path = Path(signature_map_path)
    if not path.exists():
        return ""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return path.read_text(encoding="utf-8")
    return json.dumps(data, indent=2, sort_keys=True)


def build_prompt(source_code: str, source_name: str, harness: bool, signature_map: str = "") -> str:
    if harness:
        signature_notes = ""
        if signature_map.strip():
            signature_notes = rf"""

Signature map for translated solution interfaces:
<signature_map>
{signature_map}
</signature_map>

Use this map as the source of truth for the exported C call surface. If the
translated solution introduces explicit length parameters for Dafny sequences
or arrays, call those wrappers with the required length argument(s) instead of
guessing a direct pointer-only signature.
"""
        return rf"""You are translating a Dafny test case into a standalone C test harness.

Rules:
1. Output exactly one complete C source file.
2. Do not use markdown fences, bullet lists, or explanations.
3. Do not emit ACSL or Frama-C annotations.
4. Preserve the executable behavior and test intent of the Dafny source.
5. Translate every Dafny `assert` or `expect` into a C runtime check.
6. If the Dafny file contains `Main`, translate it into `int main(void)` and call the test routine(s).
7. The harness must assume the translated solution C file will be compiled alongside it.
8. Declare `extern` prototypes for the solution functions that the test case calls, inferring their names and types from the Dafny code.
9. Do not reimplement the solution function bodies; only write the test harness.
10. Prefer idiomatic, compilable C11.
11. If helper functions or small helper types are needed, include them in the same file.
12. Include any standard headers needed by the generated code.
13. If a signature map is provided, treat it as authoritative for function names, parameter order, return conventions, and any explicit length arguments.
14. When the Dafny source has multiple returns, preserve that test intent through the mapped wrapper or out-parameter convention instead of guessing a new call shape.

Here is the Dafny source file `{source_name}`:
<dafny_code>
{source_code}
</dafny_code>
{signature_notes}

Harness notes:
- Use `assert(...)` or an equivalent check helper for every expectation.
- Prefer direct C scalars and pointer-plus-length parameters over custom wrapper structs.
- Do not invent helper type names like `HarnessSeqInt` or `HarnessIntArray` unless the Dafny file already introduces them.
- If a result is a sequence, compare it with a small helper that works on plain arrays and explicit lengths.
- If a result is floating point, compare with a small tolerance.
- Preserve all test cases, even when they are written using `expect`.

Return only the translated C test harness."""
    return rf"""You are translating a Dafny test case into plain C.

Rules:
1. Output exactly one complete C source file.
2. Do not use markdown fences, bullet lists, or explanations.
3. Do not emit ACSL or Frama-C annotations.
4. Preserve the executable behavior and test intent of the Dafny source.
5. Prefer idiomatic, compilable C11.
6. If helper functions are needed, include them in the same file.
7. Include any standard headers needed by the generated code.

Here is the Dafny source file `{source_name}`:
<dafny_code>
{source_code}
</dafny_code>

Return only the translated C code."""


def extract_code(text: str) -> str:
    if not text:
        return ""
    patterns = [
        r"<c_code>(.*?)</c_code>",
        r"<code>(.*?)</code>",
        r"```c\n?(.*?)```",
        r"```\n?(.*?)```",
    ]
    for pattern in patterns:
        match = re.search(pattern, text, re.DOTALL | re.IGNORECASE)
        if match:
            return match.group(1).strip()
    return text.strip()


def sanitize_output_name(value: str) -> str:
    cleaned = value.strip().replace(" ", "-")
    return cleaned or "translation"


def translate_file(
    client: OpenAI,
    model: str,
    temperature: float,
    source_path: Path,
    harness: bool,
    signature_map: str = "",
    request_headers: dict[str, str] | None = None,
) -> dict:
    source_code = source_path.read_text(encoding="utf-8")
    prompt = build_prompt(source_code, source_path.name, harness, signature_map)
    started = time.time()
    request_kwargs = {
        "model": model,
        "messages": [
            {"role": "system", "content": "You translate Dafny programs into plain C."},
            {"role": "user", "content": prompt},
        ],
        "temperature": temperature,
        "max_completion_tokens": 8000,
    }
    if request_headers:
        request_kwargs["extra_headers"] = request_headers
    response = client.chat.completions.create(**request_kwargs)
    elapsed = time.time() - started
    content = response.choices[0].message.content or ""
    code = extract_code(content)
    return {
        "source_path": str(source_path),
        "model": model,
        "temperature": temperature,
        "seconds": elapsed,
        "prompt_tokens": getattr(response.usage, "prompt_tokens", 0) if response.usage else 0,
        "completion_tokens": getattr(response.usage, "completion_tokens", 0) if response.usage else 0,
        "raw_response": content,
        "code": code,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Translate Dafny test cases to plain C")
    parser.add_argument("--input-dir", default="input", help="Base input directory")
    parser.add_argument("--input-folder", help="Specific subfolder under --input-dir")
    parser.add_argument("--output-dir", default="translated-c", help="Directory for generated C files")
    parser.add_argument("--model", default=DEFAULT_MODEL, help="OpenAI model to use")
    parser.add_argument("--temperature", type=float, default=0.0, help="Sampling temperature")
    parser.add_argument("--provider", default=DEFAULT_PROVIDER, choices=["openai", "openrouter"], help="Model provider to use")
    parser.add_argument("--openai-key", help="OpenAI API key")
    parser.add_argument("--openrouter-key", help="OpenRouter API key")
    parser.add_argument("--openrouter-referer", default="", help="Optional HTTP-Referer header for OpenRouter attribution")
    parser.add_argument("--openrouter-title", default="", help="Optional X-OpenRouter-Title header for OpenRouter attribution")
    parser.add_argument("--no-recursive", action="store_false", dest="recursive", help="Only translate files in the top-level folder")
    parser.add_argument("--patterns", nargs="+", default=["*.dfy"], help="Filename patterns to translate")
    parser.add_argument("--overwrite", action="store_true", help="Overwrite existing output files")
    parser.add_argument("--manifest-name", default="translation_manifest.json", help="Name of the JSON run manifest")
    parser.add_argument("--test-harness", action="store_true", help="Translate Dafny test files into C test harnesses")
    parser.add_argument("--signature-map", help="Optional JSON file describing translated solution interfaces for harness generation")
    parser.set_defaults(recursive=True)
    args = parser.parse_args()

    config = Config()
    provider = (args.provider or DEFAULT_PROVIDER).strip().lower()
    if provider == "openrouter":
        api_key = (
            args.openrouter_key
            or os.environ.get("OPENROUTER_API_KEY")
            or args.openai_key
            or config.openai_api_key
            or os.environ.get("OPENAI_API_KEY")
        )
    else:
        api_key = args.openai_key or config.openai_api_key or os.environ.get("OPENAI_API_KEY")
    if not api_key:
        key_name = "OPENROUTER_API_KEY" if provider == "openrouter" else "OPENAI_API_KEY"
        print(f"Error: API key required. Set {key_name} or pass the corresponding command-line flag.")
        return 1
    if looks_like_placeholder_api_key(api_key):
        provider_label = "OpenRouter" if provider == "openrouter" else "OpenAI"
        print(f"Error: API key looks like a placeholder. Set a real {provider_label} key and retry.")
        return 1

    input_root = Path(args.input_dir)
    if args.input_folder:
        input_root = input_root / args.input_folder
    if not input_root.exists():
        print(f"Error: input folder not found: {input_root}")
        return 1

    output_root = Path(args.output_dir)
    if args.input_folder:
        output_root = output_root / sanitize_output_name(args.input_folder)
    output_root.mkdir(parents=True, exist_ok=True)

    client = create_client(provider, api_key)
    files = collect_input_files(input_root, args.recursive, args.patterns)
    if not files:
        print(f"No matching files found under {input_root}")
        return 1

    signature_map = load_signature_map(args.signature_map)

    manifest = {
        "model": args.model,
        "provider": provider,
        "temperature": args.temperature,
        "input_root": str(input_root),
        "output_root": str(output_root),
        "signature_map": args.signature_map or "",
        "openrouter_referer": args.openrouter_referer or "",
        "openrouter_title": args.openrouter_title or "",
        "files": [],
    }

    for idx, source_path in enumerate(files, start=1):
        rel_path = source_path.relative_to(input_root)
        out_path = (output_root / rel_path).with_suffix(".c")
        out_path.parent.mkdir(parents=True, exist_ok=True)

        if out_path.exists() and not args.overwrite:
            manifest["files"].append({
                "source": str(source_path),
                "output": str(out_path),
                "skipped": True,
                "reason": "output exists",
            })
            print(f"[{idx}/{len(files)}] skip {rel_path}")
            continue

        print(f"[{idx}/{len(files)}] translate {rel_path}")
        request_headers = None
        if provider == "openrouter":
            request_headers = {}
            if args.openrouter_referer.strip():
                request_headers["HTTP-Referer"] = args.openrouter_referer.strip()
            if args.openrouter_title.strip():
                request_headers["X-OpenRouter-Title"] = args.openrouter_title.strip()
        result = translate_file(client, args.model, args.temperature, source_path, args.test_harness, signature_map, request_headers)
        out_path.write_text(result["code"], encoding="utf-8")

        meta_path = out_path.with_suffix(".json")
        meta_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

        manifest["files"].append({
            "source": str(source_path),
            "output": str(out_path),
            "meta": str(meta_path),
            "prompt_tokens": result["prompt_tokens"],
            "completion_tokens": result["completion_tokens"],
            "seconds": result["seconds"],
            "skipped": False,
        })

    manifest_path = output_root / args.manifest_name
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"Wrote {len(files)} translations to {output_root}")
    print(f"Manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
