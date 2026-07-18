"""Main entry point for formalspecc."""

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.config import Config
from src.pipeline import ACSLPipeline
from src.mutation_testing import MutationTestingConfig
from src.report import HTMLReportGenerator, generate_translation_report
from src.differential_testing import DifferentialTestingConfig


DEFAULT_MUTATION_COMMAND_TEMPLATE = "acsl-mutation-tester --input {translated_c_path} --report {report_file}"


API_KEY_PLACEHOLDER_MARKERS = (
    "your_key",
    "your-api-key",
    "your_api_key",
    "replace_with",
    "sk-...",
    "<your",
)


def looks_like_placeholder_api_key(value: str) -> bool:
    normalized = value.strip().lower()
    if not normalized:
        return False
    return any(marker in normalized for marker in API_KEY_PLACEHOLDER_MARKERS)


def sanitize_output_name(value: str) -> str:
    cleaned = value.strip().replace(" ", "-")
    return cleaned or "run"


def main():
    import argparse
    parser = argparse.ArgumentParser(description="formalspecc: ACSL Pipeline")
    
    # Input/Output
    parser.add_argument("--input-folder", help="Input folder name")
    parser.add_argument("--folders", nargs="+", help="List of input folders")
    parser.add_argument("--output-folder", help="Output folder name")
    parser.add_argument("--input-dir", default="input", help="Base input dir")
    parser.add_argument("--output-dir", default="output", help="Base output dir")
    
    # Model
    parser.add_argument("--model", default="gpt-5.2", help="OpenAI model")
    parser.add_argument("--temperature", type=float, default=0.7, help="LLM temperature")
    parser.add_argument("--fallback-model", help="Fallback model for untranslated files")
    parser.add_argument("--fallback-temperature", type=float, help="Fallback model temperature")
    parser.add_argument("--checkpoint-every", type=int, default=0, help="Save intermediate results every N files (0 disables)")
    parser.add_argument("--resume", action="store_true", help="Skip files that already have outputs")
    parser.add_argument("--max-verify-iters", type=int, default=3, help="Max verification-improvement iterations per file")
    parser.add_argument("--enable-differential-testing", dest="enable_differential_testing", action="store_true", help="Run Dafny-to-C behavioral cross-checks")
    parser.add_argument("--skip-differential-testing", dest="enable_differential_testing", action="store_false", help="Skip Dafny-to-C behavioral cross-checks")
    parser.add_argument("--dafny-executable", default="dafny", help="Dafny CLI executable name or path")
    parser.add_argument("--dafny-backend", default="cpp", help="Dafny backend for behavioral validation builds")
    parser.add_argument("--dafny-generate-tests-mode", default="InlinedBlock", help="Mode for 'dafny generate-tests' when no custom command template is supplied")
    parser.add_argument("--dafny-test-backend", default="py", help="Backend for executing generated Dafny tests")
    parser.add_argument("--c-compiler", default="gcc", help="C compiler for generated validation harnesses")
    parser.add_argument("--dtest-command-template", help="Shell command template that produces a test vector JSON file. Available placeholders: {dafny_file}, {work_dir}, {vectors_file}, {backend}")
    parser.add_argument("--dafny-build-command-template", help="Shell command template for building the Dafny file. Available placeholders: {dafny_file}, {work_dir}, {backend}")
    parser.add_argument("--dafny-generated-tests-command-template", help="Shell command template for running generated Dafny tests. Available placeholders: {dafny_file}, {work_dir}, {vectors_file}, {backend}")
    parser.add_argument("--translated-harness-dir", default=os.environ.get("PRETRANSLATED_HARNESS_DIR", ""), help="Directory with pretranslated C test harnesses for end-to-end validation")
    parser.add_argument("--enable-mutation-testing", dest="enable_mutation_testing", action="store_true", help="Run specification mutation testing on translated ACSL outputs")
    parser.add_argument("--skip-mutation-testing", dest="enable_mutation_testing", action="store_false", help="Skip specification mutation testing on translated ACSL outputs")
    parser.add_argument("--skip-roundtrip", dest="enable_roundtrip", action="store_false", help="Skip the Dafny back-translation round-trip check")
    parser.add_argument("--mutation-command-template", help="Shell command template for mutation testing. Available placeholders: {translated_c_path}, {translated_c_code}, {translated_c_filename}, {source_file}, {source_code}, {work_dir}, {report_file}")
    parser.add_argument("--mutation-timeout", type=int, default=600, help="Timeout for mutation testing command in seconds")
    parser.add_argument("--mutation-report-name", default="mutation_report.json", help="Name of the mutation testing report file")
    
    # Other
    parser.add_argument("--source-lang", default="dafny", help="Source language")
    parser.add_argument("--target-lang", default="ACSL", help="Target language")
    parser.add_argument("--skip-verification", action="store_true", help="Skip Frama-C")
    parser.add_argument("--debug", action="store_true", help="Enable debug output")
    parser.add_argument("--no-open-report", action="store_true", help="Don't open HTML")
    parser.add_argument("--openai-key", help="OpenAI API key")
    parser.set_defaults(enable_differential_testing=True, enable_mutation_testing=True, enable_roundtrip=True)
    args = parser.parse_args()

    if args.enable_mutation_testing and not (args.mutation_command_template or "").strip():
        args.mutation_command_template = DEFAULT_MUTATION_COMMAND_TEMPLATE
    
    # API key
    config = Config()
    api_key = args.openai_key or config.openai_api_key or os.environ.get("OPENAI_API_KEY")
    if not api_key:
        print("Error: API key required. Use --openai-key or OPENAI_API_KEY")
        sys.exit(1)
    if looks_like_placeholder_api_key(api_key):
        print("Error: OPENAI_API_KEY appears to be a placeholder. Set a real API key and retry.")
        sys.exit(1)
    
    # Folders
    folders = []
    output_mappings = []
    if args.input_folder and args.folders:
        parser.error("Use either --input-folder or --folders, not both.")

    if args.input_folder:
        folders = [args.input_folder]
        output_base = args.output_dir
        output_name = sanitize_output_name(args.output_folder or args.input_folder)
        output_mappings = [(args.input_folder, output_name)]
    elif args.folders:
        folders = args.folders
        output_base = args.output_dir
        output_mappings = list(zip(args.folders, args.folders))
    else:
        output_base = args.output_dir
        if os.path.exists(args.input_dir):
            folders = sorted([d for d in os.listdir(args.input_dir) if os.path.isdir(os.path.join(args.input_dir, d))])
            output_mappings = list(zip(folders, folders))
    
    print(f"formalspecc - {args.model} (temp={args.temperature})")
    if args.fallback_model:
        fb_temp = args.fallback_temperature if args.fallback_temperature is not None else args.temperature
        print(f"Fallback model: {args.fallback_model} (temp={fb_temp})")
    print(f"Folders: {folders or 'all in ' + args.input_dir}")
    print(
        "Checks: Frama-C "
        + ("on" if not args.skip_verification else "off")
        + ", behavioral validation "
        + ("on" if args.enable_differential_testing else "off")
        + ", round-trip "
        + ("on" if args.enable_roundtrip else "off")
        + ", mutation testing "
        + ("on" if args.enable_mutation_testing else "off")
    )
    print("=" * 50)
    
    # Run
    pipeline = ACSLPipeline(
        model=args.model, temperature=args.temperature,
        source_lang=args.source_lang, input_dir=args.input_dir,
        output_dir=output_base, skip_verif=args.skip_verification,
        api_key=api_key, debug=args.debug,
        fallback_model=args.fallback_model,
        fallback_temperature=args.fallback_temperature,
        checkpoint_every=args.checkpoint_every,
        resume=args.resume,
        max_verify_iters=args.max_verify_iters,
        roundtrip_enabled=args.enable_roundtrip,
        target_lang=args.target_lang,
        dafny_executable=args.dafny_executable,
        differential_testing=DifferentialTestingConfig(
            enabled=args.enable_differential_testing,
            dafny_executable=args.dafny_executable,
            backend=args.dafny_backend,
            generate_tests_mode=args.dafny_generate_tests_mode,
            test_backend=args.dafny_test_backend,
            c_compiler=args.c_compiler,
            dtest_command_template=args.dtest_command_template or "",
            dafny_build_command_template=args.dafny_build_command_template or "",
            dafny_generated_tests_command_template=args.dafny_generated_tests_command_template or "",
        ),
        mutation_testing=MutationTestingConfig(
            enabled=args.enable_mutation_testing,
            command_template=args.mutation_command_template or "",
            timeout=args.mutation_timeout,
            report_name=args.mutation_report_name,
        ),
        translated_harness_dir=args.translated_harness_dir or "",
    )
    
    pipeline.run(output_mappings or folders)
    
    # Reports
    print("\nGenerating reports...")
    for input_name, output_name in (output_mappings or [(f, f) for f in (folders or [])]):
        out_dir = os.path.join(output_base, output_name)
        if os.path.exists(out_dir):
            stats = pipeline.metrics.get_summary()
            gen = HTMLReportGenerator(out_dir)
            gen.set_config({
                "model": args.model, 
                "temp": args.temperature, 
                "folder": output_name,
                "source_lang": args.source_lang,
                "target_lang": args.target_lang,
                "initial_problems": stats.get('total_programs', 0),
                "iterations": 1,
                "programs_per_iteration": stats.get('total_programs', 0),
            })
            if pipeline.metrics.results:
                gen.set_statistics(stats)
                for r in pipeline.metrics.results:
                    gen.add_program(r.to_dict())
            gen.generate("report.html")
            generate_translation_report([r.to_dict() for r in pipeline.metrics.results],
                                      os.path.join(out_dir, "translation_report.md"))
    
    print("Done!")
    
    # Open report
    if not args.no_open_report and (output_mappings or folders):
        first_output = output_mappings[0][1] if output_mappings else folders[0]
        path = os.path.join(output_base, first_output, "report.html")
        if os.path.exists(path):
            if sys.platform == "win32":
                os.startfile(path)
            else:
                import webbrowser
                webbrowser.open(f"file://{os.path.abspath(path)}")


if __name__ == "__main__":
    main()
