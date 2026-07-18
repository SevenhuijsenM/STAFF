# Prompts for translation between Dafny and C+ACSL

def _normalize_lang(value: str) -> str:
    return (value or "").strip().lower()

def generate_improvement_prompt_verification(
    source_code: str, current_translation: str, verification_feedback: str,
    source_lang: str = "dafny", target_lang: str = "acsl") -> str:
    if _normalize_lang(target_lang) == "dafny":
        return rf"""You are repairing a Dafny file after verification failure.

Goal:
1. Make the Dafny code syntactically valid.
2. Preserve the original C + ACSL functionality and contract intent.
3. Improve Dafny verification success.

Return only one complete Dafny file inside <dafny_code> ... </dafny_code>.
Do not return analysis, explanations, markdown fences, or any prose outside the tags.

Here is the original C + ACSL code:
<source_code>
{source_code}
</source_code>

Here is the current Dafny translation:
<dafny_translation>
{current_translation}
</dafny_translation>

Here is the Dafny verifier feedback:
<dafny_feedback>
{verification_feedback}
</dafny_feedback>

Mandatory Dafny rules:
- Output valid Dafny 4 syntax.
- Keep preconditions as `requires`, postconditions as `ensures`, loop invariants as `invariant`, and frame intent as `modifies` or `reads` where appropriate.
- Prefer simple verifiable formulations over clever but brittle ones.
- If helper predicates or functions are needed, define them explicitly before use.
- Preserve executable behavior while repairing contracts and invariants.

Return exactly:
<dafny_code>
[one complete repaired Dafny file]
</dafny_code>
"""
    return rf"""You are repairing a C + ACSL file for Frama-C/WP.

Goal:
1. Make the ACSL valid for Frama-C parsing and typing.
2. Preserve the original Dafny functionality.
3. Improve proof success.

Return only one complete repaired C file inside <c_code_with_acsl> ... </c_code_with_acsl>.
Do not return analysis, explanations, markdown fences, or any prose outside the tags.
If you are unsure, still return the best repaired code you can produce. Do not return an empty response.

Here is the original Dafny code:
<dafny_code>
{source_code}
</dafny_code>

Here is the current C translation:
<c_translation>
{current_translation}
</c_translation>

Here is the Frama-C feedback:
<frama_c_feedback>
{verification_feedback}
</frama_c_feedback>

Mandatory Frama-C ACSL rules:
- Use only `/*@ ... */` and `//@ ...` annotations.
- Do not put ordinary comments on the same line as `//@` annotations.
- Do not nest ACSL annotations.
- Do not use chained inequalities; write `0 <= i && i <= n`.
- Do not use unsupported constructs such as `\length(pointer)` or `\strlen(pointer)`.
- Do not use undeclared helper functions or predicates from contracts.
- Keep one ACSL assertion per annotation comment.
- If helper predicates or logic functions are needed, define them explicitly before use.
- Prefer simple Frama-C-friendly invariants and assertions over compact but fragile ones.

Default ACSL patterns:
- Function contract: `/*@ requires P; assigns A; ensures Q; */`
- Loop contract: `/*@ loop invariant I; loop assigns A; loop variant V; */`
- Assertion: `//@ assert P;`
- Quantifier: `\forall integer i; range ==> property`
- Pointer validity: `\valid(p)` or `n == 0 || \valid_read(p + (0 .. n-1))`
- Return value: `\result`
- Pre-state value: `\old(expr)`

Repair priorities:
1. Fix malformed ACSL syntax and typing first.
2. Fix missing helper declarations/specifications.
3. Strengthen contracts, invariants, and assertions only after the file is Frama-C-valid.
4. Preserve the original control-flow intent from Dafny.

Common failure patterns to eliminate if present:
- malformed ACSL comments
- unsupported pointer/string length logic
- helper calls with no declaration/specification
- multiple ACSL assertions merged into one comment
- code that compiles as C but cannot be parsed by Frama-C because of annotation errors

Return exactly:
<c_code_with_acsl>
[one complete repaired C file]
</c_code_with_acsl>
"""

def generate_improvement_prompt_compilation(
    source_code: str, current_translation: str, translation_feedback: str,
    source_lang: str = "dafny", target_lang: str = "acsl") -> str:
    if _normalize_lang(target_lang) == "dafny":
        return rf"""
You are tasked with fixing a Dafny file that was translated from C + ACSL but does not resolve or verify correctly.

Here is the original C + ACSL source:
<source_code>
{source_code}
</source_code>

Here is the translated Dafny code:
<dafny_code>
{current_translation}
</dafny_code>

Here is the Dafny resolver/compiler output:
<dafny_output>
{translation_feedback}
</dafny_output>

Please fix syntax, declarations, contracts, invariants, helper definitions, and typing issues while preserving the original source intent.
Preserve the original Dafny surface form when possible: if the source was an executable Dafny method with an explicit result and postcondition, keep it as a `method` with `returns (...)` and `ensures` rather than silently collapsing it into a pure `function`.

Output format:
<dafny_code>
[corrected Dafny code only]
</dafny_code>

<explanation>
[brief explanation]
</explanation>
"""
    return rf"""
You are tasked with improving a C file that was translated from Dafny code but is not compiling or verifying correctly. You will be provided with the original Dafny code, the translated C code, and the compiler output. Your goal is to analyze the issues, make necessary improvements to the C code, and provide an explanation of the changes.

Here is the original Dafny code:
<dafny_code>
{source_code}
</dafny_code>

Here is the translated C code that is not compiling or verifying:
<c_code>
{current_translation}
</c_code>

Here is the compiler output showing the errors:
<compiler_output>
{translation_feedback}
</compiler_output>

Please follow these steps:

1. Carefully analyze the compiler output to identify the specific errors and issues.

2. Compare the Dafny code with the C code to understand the translation and potential sources of errors.

3. Make necessary improvements to the C code to address the compilation and verification issues. Focus on:
   - Correcting syntax errors
   - Adjusting function signatures and return types
   - Fixing logical errors in the translated code
   - Ensuring proper use of ACSL annotations

4. The improved code MUST use Frama-C-compatible ACSL only. Follow these rules strictly:
   - Use only `/*@ ... */` and `//@ ...` for ACSL.
   - Do not append ordinary `// ...` comments to `//@` annotation lines.
   - Do not use chained inequalities; rewrite them with `&&`.
   - Do not use unsupported ACSL constructs on raw pointers (for example `\length(pointer)`).
   - Do not emit prose, markdown fences, or explanatory text inside the code block.
   - If the previous code begins with stray formatting artifacts like a leading `c`, remove them.
   - Keep annotations simple and syntactically valid before trying to optimize proof strength.

5. Use the following ACSL syntax patterns as defaults:
   - Function contract: `/*@ requires P; assigns A; ensures Q; */`
   - Loop contract: `/*@ loop invariant I; loop assigns A; loop variant V; */`
   - Assertion: `//@ assert P;`
   - Quantifier: `\forall integer i; range ==> property`
   - Pointer validity: `\valid(p)` or `n == 0 || \valid_read(p + (0 .. n-1))`

6. Avoid these invalid or fragile patterns:
   - `\length(pointer)` or `\strlen(pointer)`
   - `0 <= i <= n`
   - undeclared helper predicates/functions used from contracts
   - multiple ACSL assertions in one annotation comment
   - prose or markdown fences inside the code output

7. Provide the improved C code that should compile and verify correctly. Include all necessary ACSL annotations.

8. Explain the changes you made to the C code and why they were necessary. Reference specific parts of the Dafny code, original C code, and compiler output in your explanation.

Present your response in the following format:

<c_code_with_acsl>
[Insert the improved C code here, including all necessary ACSL annotations]
</c_code_with_acsl>

<explanation>
[Provide a detailed explanation of the changes made to the C code, referencing specific parts of the Dafny code, original C code, and compiler output]
</explanation>

Remember to maintain the original structure and intent of the Dafny code while making the necessary adjustments for proper C syntax and Frama-C-valid ACSL annotations. Ensure that your improved C code should compile without errors and should not contain malformed ACSL.
"""

def generate_initial_prompt(source_code: str, source_lang: str = "dafny", target_lang: str = "acsl") -> str:
    if _normalize_lang(target_lang) == "dafny":
        return rf"""You are tasked with converting a C program annotated with ACSL into Dafny. Follow these instructions carefully.

<source_program>
{source_code}
</source_program>

Requirements:
1. Translate executable behavior from C into idiomatic Dafny.
2. Translate ACSL contracts into Dafny contracts:
   - `requires` -> `requires`
   - `ensures` -> `ensures`
   - `assigns` -> `modifies` when there are mutable locations
   - loop invariants and variants -> Dafny `invariant` and `decreases`
3. Replace pointer-length conventions with Dafny arrays or sequences as appropriate.
4. Preserve the contract intent, including membership, ordering, frame, and loop properties.
5. Output one complete Dafny file only.
6. Do not return explanations.

Output format:
<dafny_code>
[full Dafny translation]
</dafny_code>
"""
    return rf"""You are tasked with converting a Dafny program to C code with ACSL (ANSI/ISO C Specification Language) specifications. Follow these instructions carefully to complete the task accurately and thoroughly:

First, here is the Dafny program you need to convert:

<dafny_program>
{source_code}
</dafny_program>

To convert this Dafny program to C with ACSL specifications, follow these steps:

1. **Analyze the Dafny Program:**
   - Identify all methods/functions, their parameters, return types, and any Dafny-specific constructs such as:
     - **requires** (preconditions)
     - **ensures** (postconditions)
     - **modifies** clauses
     - **loop invariants** and loop variant expressions
   - Determine whether subfunctions are present or necessary. If a single Dafny function naturally breaks down into multiple smaller functions in C, each should be declared and annotated with its own preconditions and postconditions.
   - Treat every Dafny `requires`, `ensures`, `reads`, `modifies`, loop invariant, and termination hint as semantically important contract information that must be preserved in the C + ACSL output whenever a direct ACSL counterpart exists.
   - When the source behavior corresponds to an executable Dafny `method` with a returned value, prefer reconstructing a Dafny `method` on the way back rather than a pure `function`, especially when that method had an explicit `ensures` clause.

2. **Convert the Dafny Code to C:**
   - Translate each Dafny function into a corresponding C function (or multiple C functions if needed).
   - Preserve the original Dafny method/function name as the exported C symbol whenever possible; only change the entry point `Main` to `main` and make the smallest necessary identifier adjustments for C legality.
   - Map Dafny types to C types (e.g., `int` in Dafny to `int` in C). If a Dafny type does not map directly, explain the choice or approximation in your explanation.
   - Ensure all variables are properly declared in C.
   - Preserve the logic and control flow of the original Dafny code, including any loops and branches.
   - Do not erase Dafny postconditions by turning them into plain C runtime checks only; if the source has an `ensures` clause, encode it as ACSL `ensures` on the relevant C function.
   - Do not drop contracts just because the executable body is simple. Even a one-line Dafny method/function should keep its specification in ACSL.
   - If the Dafny source is a pure function, prefer a C function plus ACSL specification that still exposes the logical contract rather than omitting the contract entirely.

3. **Create or Identify Subfunctions if Necessary:**
   - If the Dafny code has multiple functions or you find it beneficial to break a large function into smaller parts, create separate C functions accordingly.
   - Each subfunction must have its own declarations, definitions, and logic that match the intent of the original Dafny code.
   - Preserve the executable/specification split from the Dafny source as much as possible. If the original code was a method with an output parameter and postcondition, do not erase that structure by representing it only as a pure logical helper.

4. **Add ACSL Specifications (Including Loop Invariants and Variants):**
   - For each function (including subfunctions):
      - Convert Dafny `requires` clauses to ACSL `requires` clauses.
      - Convert Dafny `ensures` clauses to ACSL `ensures` clauses.
      - Convert Dafny `modifies` clauses to ACSL `assigns` clauses (if applicable).
      - Place ACSL specifications as block comments starting with `/*@` and ending with `@*/` immediately above each function.
      - Never omit an available ACSL contract when it can be stated from the Dafny source.
      - Prefer explicit ACSL postconditions over runtime-only assertions when the original Dafny code has a postcondition.
   - For each loop in your C code:
     - Translate or infer the corresponding Dafny loop invariants and variants into ACSL. 
     - Place them directly above the loop in the form:
       ```
       /*@
         loop invariant ...;
         loop assigns ...;
         loop variant ...;
       */
       ```
      - If Dafny's loop specifications are absent or incomplete, infer invariants that correctly capture the loop's behavior (e.g., variable bounds, relationships between variables, etc.). Do this also for helper functions.

5. **Frama-C ACSL Compatibility Rules (Mandatory):**
   - Output Frama-C-compatible ACSL only, not generic pseudo-ACSL.
   - Use only valid ACSL comment forms: `/*@ ... */` and `//@ ...`.
   - Never add ordinary comments on the same line as a `//@` annotation.
   - Never use chained inequalities like `0 <= i <= n`; always write `0 <= i && i <= n`.
   - Do not use unsupported pointer-length constructs such as `\length(ptr)`.
   - Do not invent logic functions, predicates, or ghost constructs unless you define them explicitly in valid ACSL syntax.
   - Keep one ACSL assertion per annotation comment.
   - Prefer simple, explicit Frama-C-friendly assertions and loop invariants over compact but ambiguous expressions.
   - When modeling strings or arrays in C, make memory validity and bounds explicit using `\valid`, `\valid_read`, lengths, and separation where needed.
   - If translating from Dafny mathematical integers or reals, add the necessary C-side assumptions or reformulations to avoid invalid machine-level reasoning.

6. **ACSL Syntax Guide (Use These Patterns):**
   - Function contract: `/*@ requires P; assigns A; ensures Q; */`
   - Loop contract: `/*@ loop invariant I; loop assigns A; loop variant V; */`
   - Assertion: `//@ assert P;`
   - Quantifier: `\forall integer i; range ==> property`
   - Pointer validity: `\valid(p)` or `n == 0 || \valid_read(p + (0 .. n-1))`
   - Return-value reference: `\result`
   - Pre-state reference: `\old(expr)`

7. **Common Invalid Patterns to Avoid:**
   - `\length(pointer)` or `\strlen(pointer)`
   - chained inequalities such as `0 <= i <= n`
   - undeclared helper predicates/functions used from contracts
   - multiple ACSL assertions in one annotation comment
   - prose or markdown fences inside `<c_code_with_acsl>`

8. **Format Your Output:**
   - Begin your response with `<c_code_with_acsl>` tags.
   - Include any necessary C headers (e.g., `#include <limits.h>` if using `INT_MAX` or similar constants).
   - Provide the fully annotated C code, with:
      - ACSL contracts for each function (including subfunctions).
      - Loop invariants and variants for each loop, if applicable.
   - Output code only inside the tags: no markdown fences, no prose, no bullet lists.
   - End your response with `</c_code_with_acsl>` tags.

9. **Explanation of the Conversion Process:**
   - After providing the annotated C code, give a concise explanation of your approach. Summarize:
      - Any Dafny-specific features that required special handling (e.g., maps, sets, sequences, ghost variables).
      - Any inferred or newly introduced loop invariants or function-level preconditions/postconditions.
      - The rationale behind creating subfunctions, if you did so, and how their specifications were derived.

Remember to preserve the logic and behavior of the original Dafny program in your C implementation. If you encounter any Dafny-specific features that don't have direct equivalents in C or ACSL, explain how you addressed them in your explanation. A candidate that compiles as C but contains malformed ACSL is not acceptable.

Begin your conversion now, following the steps outlined above.
"""

def generate_verify_proof_prompt(dafny_code: str, c_translation: str) -> str:
    return rf"""
You are tasked with formally verifying a C translation of a Dafny file using Frama-C. You will be provided with the original Dafny code and the C translation. Your goal is to analyze the code and provide feedback on its verifiability.

Here is the original Dafny code:
<dafny_code>
{dafny_code}
</dafny_code>

Here is the C translation to verify:
<c_code>
{c_translation}
</c_code>

Please analyze this code and provide feedback in the following format:

<verification_analysis>
- Does the code compile with Frama-C?
- Are all ACSL annotations syntactically correct?
- What proof obligations are generated?
- Which goals are provable and which are not?
- Suggestions for improving verifiability
</verification_analysis>

<recommendations>
Specific recommendations to improve the formal verification of this code.
</recommendations>

Focus on identifying any issues that may prevent successful formal verification with Frama-C.
"""
