"""
Metrics interface for formal specification translation evaluation.

This module provides a comprehensive set of metrics for evaluating
formal specification translation from source languages (e.g., Dafny)
to target languages with formal specifications (e.g., ACSL-annotated C with Frama-C).
"""

import os
import re
import json
import time
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Any, Optional
from enum import Enum
from .verify import compile_c as run_compile_c
from .verify import verify_with_wp as run_verify_with_wp


class MetricCategory(Enum):
    COMPILATION = "compilation"
    VERIFICATION = "verification"
    TRANSLATION = "translation"
    COST = "cost"
    CODE_QUALITY = "code_quality"
    SPECIFICATION = "specification"


@dataclass
class MetricResult:
    name: str
    value: Any
    category: MetricCategory
    description: str
    details: Dict[str, Any] = field(default_factory=dict)


@dataclass
class TranslationMetrics:
    program_id: str = ""
    source_language: str = ""
    target_language: str = ""
    
    compiles: bool = False
    compilation_attempts: int = 0
    compilation_time: float = 0.0
    compilation_errors: List[str] = field(default_factory=list)
    
    verified: bool = False
    proof_obligations: int = 0
    proven_obligations: int = 0
    unproven_obligations: int = 0
    verification_time: float = 0.0
    prover_used: str = ""
    
    translation_success: bool = False
    translation_attempts: int = 0
    
    input_tokens: int = 0
    output_tokens: int = 0
    total_cost: float = 0.0
    
    source_lines: int = 0
    target_lines: int = 0
    function_count: int = 0
    specification_count: int = 0
    
    has_preconditions: bool = False
    has_postconditions: bool = False
    has_invariants: bool = False
    precondition_count: int = 0
    postcondition_count: int = 0
    invariant_count: int = 0
    
    dafny_requires: int = 0
    dafny_ensures: int = 0
    dafny_invariant: int = 0
    dafny_decreases: int = 0
    dafny_modifies: int = 0
    
    source_code: str = ""
    target_code: str = ""
    
    extra: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'TranslationMetrics':
        return cls(**{k: v for k, v in data.items() if k in cls.__dataclass_fields__})


class MetricsCalculator:
    PRICE_PER_1K_INPUT_TOKENS = 0.01
    PRICE_PER_1K_OUTPUT_TOKENS = 0.03
    
    def __init__(self):
        self.results: List[TranslationMetrics] = []
    
    def calculate_cost(self, input_tokens: int, output_tokens: int) -> float:
        return (input_tokens / 1000) * self.PRICE_PER_1K_INPUT_TOKENS + \
               (output_tokens / 1000) * self.PRICE_PER_1K_OUTPUT_TOKENS

    def _extract_acsl_annotations(self, code: str) -> List[str]:
        if not code:
            return []
        blocks = re.findall(r'/\*@.*?\*/', code, flags=re.DOTALL)
        lines = re.findall(r'//@.*', code)
        return blocks + lines
    
    def count_specifications(self, code: str) -> Dict[str, int]:
        annotations = self._extract_acsl_annotations(code)
        joined = "\n".join(annotations)

        assigns_total = len(re.findall(r'\bassigns\b', joined))
        loop_assigns = len(re.findall(r'\bloop\s+assigns\b', joined))

        specs = {
            'requires': len(re.findall(r'\brequires\b', joined)),
            'ensures': len(re.findall(r'\bensures\b', joined)),
            'loop_invariant': len(re.findall(r'\bloop\s+invariant\b', joined)),
            'assert': len(re.findall(r'\bassert\b', joined)),
            'decreases': len(re.findall(r'\bdecreases\b|\bloop\s+variant\b', joined)),
            # Frame metric should track function-level assigns only.
            'assigns': max(assigns_total - loop_assigns, 0),
            'loop_assigns': loop_assigns,
        }
        return specs
    
    def analyze_code(self, code: str) -> Dict[str, Any]:
        lines = code.splitlines()
        non_empty_lines = [l for l in lines if l.strip()]
        
        function_pattern = r'\b(int|void|bool|char|float|double|long|short|unsigned)\s+\w+\s*\([^)]*\)\s*\{'
        functions = re.findall(function_pattern, code)
        
        specs = self.count_specifications(code)
        
        return {
            'total_lines': len(lines),
            'non_empty_lines': len(non_empty_lines),
            'function_count': len(functions),
            'specifications': specs,
            'has_preconditions': specs['requires'] > 0,
            'has_postconditions': specs['ensures'] > 0,
            'has_invariants': specs['loop_invariant'] > 0,
            'total_specifications': sum(specs.values()),
        }
    
    def compile_with_frama_c(self, code: str, output_file: Optional[str] = None) -> tuple:
        if not code:
            return False, ["No code provided"], 0.0

        start_time = time.time()
        success, err = run_compile_c(c_code=code, timeout=30)
        compilation_time = time.time() - start_time
        errors = [err.strip()] if err and err.strip() else []
        return success, errors, compilation_time
    
    def verify_with_wp(self, code: str, prover: str = "Alt-Ergo", 
                       output_file: Optional[str] = None) -> Dict[str, Any]:
        if not code:
            return {'verified': False, 'error': 'No code provided'}
        result = run_verify_with_wp(c_code=code, timeout=120, prover=prover)
        return {
            'verified': result.get('verified', False),
            'proof_obligations': result.get('proof_obligations', 0),
            'proven_obligations': result.get('proven_obligations', 0),
            'unproven_obligations': result.get('unproven_obligations', 0),
            'verification_time': result.get('verification_time', 0.0),
            'prover_used': result.get('prover_used', prover),
            'output': result.get('output', ''),
        }
    
    def evaluate_translation(self, source_code: str, target_code: str,
                            input_tokens: int, output_tokens: int,
                            program_id: str = "",
                            source_lang: str = "dafny",
                            target_lang: str = "acsl",
                            pre_compiled: bool = None,
                            pre_verified: bool = None,
                            pre_proof_obligations: int = None,
                            pre_proven: int = None,
                            pre_unproven: int = None,
                            dafny_stats: Dict = None,
                            src_code: str = "",
                            tgt_code: str = "") -> TranslationMetrics:
        metrics = TranslationMetrics(
            program_id=program_id,
            source_language=source_lang,
            target_language=target_lang,
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            total_cost=self.calculate_cost(input_tokens, output_tokens),
        )
        
        source_analysis = self.analyze_code(source_code or "")
        target_analysis = self.analyze_code(target_code or "")
        
        metrics.source_lines = source_analysis['total_lines']
        metrics.target_lines = target_analysis['total_lines']
        metrics.function_count = target_analysis['function_count']
        metrics.specification_count = target_analysis['total_specifications']
        metrics.has_preconditions = target_analysis['has_preconditions']
        metrics.has_postconditions = target_analysis['has_postconditions']
        metrics.has_invariants = target_analysis['has_invariants']
        
        specs = target_analysis['specifications']
        metrics.precondition_count = specs['requires']
        metrics.postcondition_count = specs['ensures']
        metrics.invariant_count = specs['loop_invariant']
        
        if dafny_stats:
            metrics.dafny_requires = dafny_stats.get('requires', 0)
            metrics.dafny_ensures = dafny_stats.get('ensures', 0)
            metrics.dafny_invariant = dafny_stats.get('invariant', 0)
            metrics.dafny_decreases = dafny_stats.get('decreases', 0)
            metrics.dafny_modifies = dafny_stats.get('modifies', 0)
        
        metrics.source_code = src_code or ""
        metrics.target_code = tgt_code or ""
        
        if pre_compiled is not None:
            metrics.compiles = pre_compiled
        else:
            compiled, errors, comp_time = self.compile_with_frama_c(target_code or "")
            metrics.compiles = compiled
            metrics.compilation_errors = errors
            metrics.compilation_time = comp_time
        
        if pre_verified is not None:
            metrics.verified = pre_verified
            metrics.proof_obligations = pre_proof_obligations or 0
            metrics.proven_obligations = pre_proven or 0
            metrics.unproven_obligations = pre_unproven or 0
        elif metrics.compiles:
            verification = self.verify_with_wp(target_code or "")
            metrics.verified = verification.get('verified', False)
            metrics.proof_obligations = verification.get('proof_obligations', 0)
            metrics.proven_obligations = verification.get('proven_obligations', 0)
            metrics.unproven_obligations = verification.get('unproven_obligations', 0)
            metrics.verification_time = verification.get('verification_time', 0.0)
            metrics.prover_used = verification.get('prover_used', '')
        
        self.results.append(metrics)
        return metrics
    
    def get_summary(self) -> Dict[str, Any]:
        if not self.results:
            return {}
        
        total = len(self.results)
        compiled = sum(1 for r in self.results if r.compiles)
        verified = sum(1 for r in self.results if r.verified)
        
        return {
            'total_programs': total,
            'compilation_success_rate': compiled / total if total > 0 else 0,
            'verification_success_rate': verified / total if total > 0 else 0,
            'total_cost': sum(r.total_cost for r in self.results),
            'avg_compilation_time': sum(r.compilation_time for r in self.results) / total,
            'avg_verification_time': sum(r.verification_time for r in self.results) / total,
            'total_proof_obligations': sum(r.proof_obligations for r in self.results),
            'total_proven': sum(r.proven_obligations for r in self.results),
            'total_unproven': sum(r.unproven_obligations for r in self.results),
            'programs_with_preconditions': sum(1 for r in self.results if r.has_preconditions),
            'programs_with_postconditions': sum(1 for r in self.results if r.has_postconditions),
            'programs_with_invariants': sum(1 for r in self.results if r.has_invariants),
            'total_dafny_requires': sum(r.dafny_requires for r in self.results),
            'total_dafny_ensures': sum(r.dafny_ensures for r in self.results),
            'total_dafny_invariant': sum(r.dafny_invariant for r in self.results),
            'total_dafny_decreases': sum(r.dafny_decreases for r in self.results),
            'total_dafny_modifies': sum(r.dafny_modifies for r in self.results),
            'total_acsl_requires': sum(r.precondition_count for r in self.results),
            'total_acsl_ensures': sum(r.postcondition_count for r in self.results),
            'total_acsl_invariant': sum(r.invariant_count for r in self.results),
        }
    
    def save_results(self, output_path: str):
        os.makedirs(os.path.dirname(output_path) if os.path.dirname(output_path) else ".", exist_ok=True)
        
        data = {
            'individual_results': [r.to_dict() for r in self.results],
            'summary': self.get_summary()
        }
        
        with open(output_path, 'w') as f:
            json.dump(data, f, indent=2)


def get_all_metrics() -> List[MetricResult]:
    """Returns a list of all available metrics with descriptions."""
    metrics = [
        MetricResult(
            name="compilation_success_rate",
            value=None,
            category=MetricCategory.COMPILATION,
            description="Percentage of generated programs that compile successfully"
        ),
        MetricResult(
            name="verification_success_rate",
            value=None,
            category=MetricCategory.VERIFICATION,
            description="Percentage of programs where all proof obligations are proven"
        ),
        MetricResult(
            name="total_cost",
            value=None,
            category=MetricCategory.COST,
            description="Total API cost in USD"
        ),
        MetricResult(
            name="precondition_coverage",
            value=None,
            category=MetricCategory.SPECIFICATION,
            description="Percentage of programs with preconditions"
        ),
        MetricResult(
            name="postcondition_coverage",
            value=None,
            category=MetricCategory.SPECIFICATION,
            description="Percentage of programs with postconditions"
        ),
    ]
    return metrics


def get_metrics_by_category(category: MetricCategory) -> List[MetricResult]:
    """Returns metrics filtered by category."""
    return [m for m in get_all_metrics() if m.category == category]
