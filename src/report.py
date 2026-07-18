"""
HTML Report Generator for SpecTrans - Formal Specification Translation.

Generates comprehensive HTML reports with:
- Pipeline configuration summary
- Translation results per program
- Verification statistics
- Code snippets with syntax highlighting
- Charts and visualizations
"""

import json
import os
import datetime
from typing import Dict, List, Any, Optional
from pathlib import Path


class HTMLReportGenerator:
    def __init__(self, output_dir: str = "output"):
        self.output_dir = output_dir
        self.report_data = {
            "timestamp": datetime.datetime.now().isoformat(),
            "config": {},
            "programs": [],
            "statistics": {},
            "errors": []
        }
    
    def set_config(self, config: Dict[str, Any]):
        self.report_data["config"] = config
    
    def add_program(self, program_data: Dict[str, Any]):
        self.report_data["programs"].append(program_data)
    
    def add_error(self, error_message: str, program_id: str = None):
        self.report_data["errors"].append({
            "message": error_message,
            "program_id": program_id,
            "timestamp": datetime.datetime.now().isoformat()
        })
    
    def set_statistics(self, stats: Dict[str, Any]):
        self.report_data["statistics"] = stats
    
    def generate(self, filename: str = "report.html") -> str:
        os.makedirs(self.output_dir, exist_ok=True)
        output_path = os.path.join(self.output_dir, filename)
        
        html_content = self._build_html()
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        return output_path
    
    def _build_html(self) -> str:
        config = self.report_data.get("config", {})
        programs = self.report_data.get("programs", [])
        stats = self.report_data.get("statistics", {})
        errors = self.report_data.get("errors", [])
        
        programs_html = self._generate_programs_table(programs)
        stats_html = self._generate_statistics_section(stats)
        errors_html = self._generate_errors_section(errors)
        code_comparison_html = self._generate_code_comparison(programs)
        
        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>SpecTrans - Formal Specification Translation Report</title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/github-dark.min.css">
    <script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js"></script>
    <script>hljs.highlightAll();</script>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, sans-serif;
            line-height: 1.6;
            color: #333;
            background: #f5f5f5;
        }}
        .container {{ max-width: 1200px; margin: 0 auto; padding: 20px; }}
        
        header {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 30px;
            border-radius: 10px;
            margin-bottom: 30px;
        }}
        header h1 {{ font-size: 2.5em; margin-bottom: 10px; }}
        header .timestamp {{ opacity: 0.9; font-size: 0.9em; }}
        
        .card {{
            background: white;
            border-radius: 10px;
            padding: 25px;
            margin-bottom: 20px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        }}
        .card h2 {{
            color: #667eea;
            margin-bottom: 20px;
            padding-bottom: 10px;
            border-bottom: 2px solid #f0f0f0;
        }}
        
        .config-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 15px;
        }}
        .config-item {{
            background: #f8f9fa;
            padding: 15px;
            border-radius: 8px;
        }}
        .config-item label {{ color: #666; font-size: 0.85em; display: block; margin-bottom: 5px; }}
        .config-item value {{ font-weight: 600; color: #333; }}
        
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
            gap: 20px;
            margin-bottom: 20px;
        }}
        .stat-box {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 20px;
            border-radius: 10px;
            text-align: center;
        }}
        .stat-box.success {{ background: linear-gradient(135deg, #11998e 0%, #38ef7d 100%); }}
        .stat-box.warning {{ background: linear-gradient(135deg, #f093fb 0%, #f5576c 100%); }}
        .stat-box .value {{ font-size: 2.5em; font-weight: bold; }}
        .stat-box .label {{ opacity: 0.9; font-size: 0.9em; }}
        
        table {{ width: 100%; border-collapse: collapse; }}
        th, td {{ padding: 12px; text-align: left; border-bottom: 1px solid #eee; }}
        th {{ background: #f8f9fa; color: #667eea; font-weight: 600; }}
        tr:hover {{ background: #f8f9fa; }}
        
        .status {{
            display: inline-block;
            padding: 4px 12px;
            border-radius: 20px;
            font-size: 0.85em;
            font-weight: 600;
        }}
        .status.success {{ background: #d4edda; color: #155724; }}
        .status.failed {{ background: #f8d7da; color: #721c24; }}
        .status.pending {{ background: #fff3cd; color: #856404; }}
        
        .code-block {{
            background: #282c34;
            color: #abb2bf;
            padding: 15px;
            border-radius: 8px;
            overflow-x: auto;
            font-family: 'Monaco', 'Menlo', monospace;
            font-size: 0.85em;
            line-height: 1.5;
            max-height: 300px;
            overflow-y: auto;
        }}
        
        .error-list {{ background: #fff3cd; border-left: 4px solid #ffc107; }}
        .error-item {{ padding: 10px; border-bottom: 1px solid #ffeeba; }}
        .error-item:last-child {{ border-bottom: none; }}
        
        .progress-bar {{
            width: 100%;
            height: 20px;
            background: #e0e0e0;
            border-radius: 10px;
            overflow: hidden;
            margin: 10px 0;
        }}
        .progress-fill {{
            height: 100%;
            background: linear-gradient(90deg, #667eea 0%, #764ba2 100%);
            transition: width 0.3s ease;
        }}
        
        .tab-container {{ margin-top: 20px; }}
        .tab-buttons {{
            display: flex;
            gap: 10px;
            margin-bottom: 15px;
        }}
        .tab-btn {{
            padding: 10px 20px;
            border: none;
            background: #f0f0f0;
            cursor: pointer;
            border-radius: 5px;
            font-weight: 600;
        }}
        .tab-btn.active {{ background: #667eea; color: white; }}
        
        .hidden {{ display: none; }}
        
        footer {{
            text-align: center;
            padding: 20px;
            color: #666;
            font-size: 0.9em;
        }}
    </style>
</head>
<body>
    <div class="container">
        <header>
            <h1>SpecTrans - Formal Specification Translation Report</h1>
            <div class="timestamp">Generated: {self.report_data.get('timestamp', '')}</div>
        </header>
        
        <div class="card">
            <h2>Pipeline Configuration</h2>
            <div class="config-grid">
                <div class="config-item">
                    <label>Source Language</label>
                    <value>{config.get('source_lang', 'N/A')}</value>
                </div>
                <div class="config-item">
                    <label>Target Language</label>
                    <value>{config.get('target_lang', 'ACSL')}</value>
                </div>
                <div class="config-item">
                    <label>Model</label>
                    <value>{config.get('model', 'N/A')}</value>
                </div>
                <div class="config-item">
                    <label>Initial Problems</label>
                    <value>{config.get('initial_problems', 0)}</value>
                </div>
                <div class="config-item">
                    <label>Iterations</label>
                    <value>{config.get('iterations', 0)}</value>
                </div>
                <div class="config-item">
                    <label>Programs per Iteration</label>
                    <value>{config.get('programs_per_iteration', 0)}</value>
                </div>
            </div>
        </div>
        
        {stats_html}
        
        <div class="card">
            <h2>Translation Results</h2>
            <div class="tab-buttons">
                <button class="tab-btn active" onclick="showTab('summary')">Summary</button>
                <button class="tab-btn" onclick="showTab('code')">Code Comparison</button>
            </div>
            <div id="tab-summary" class="tab-content">
                {programs_html}
            </div>
            <div id="tab-code" class="tab-content hidden">
                {code_comparison_html}
            </div>
        </div>
        
        {errors_html}
        
        <script>
        function showTab(tabName) {{
            document.querySelectorAll('.tab-content').forEach(t => t.classList.add('hidden'));
            document.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
            document.getElementById('tab-' + tabName).classList.remove('hidden');
            event.target.classList.add('active');
        }}
        </script>
        
        <footer>
            <p>SpecTrans - Formal Specification Translation Framework</p>
        </footer>
    </div>
</body>
</html>"""
        return html
    
    def _generate_statistics_section(self, stats: Dict[str, Any]) -> str:
        if not stats:
            return ""
        
        total = stats.get('total_programs', 0)
        compiled = int(total * stats.get('compilation_success_rate', 0))
        verified = int(total * stats.get('verification_success_rate', 0))
        
        return f"""
        <div class="card">
            <h2>Statistics Overview</h2>
            <div class="stats-grid">
                <div class="stat-box">
                    <div class="value">{total}</div>
                    <div class="label">Total Programs</div>
                </div>
                <div class="stat-box success">
                    <div class="value">{compiled}</div>
                    <div class="label">Compiled ({stats.get('compilation_success_rate', 0)*100:.1f}%)</div>
                </div>
                <div class="stat-box success">
                    <div class="value">{verified}</div>
                    <div class="label">Verified ({stats.get('verification_success_rate', 0)*100:.1f}%)</div>
                </div>
                <div class="stat-box">
                    <div class="value">${stats.get('total_cost', 0):.2f}</div>
                    <div class="label">Total Cost</div>
                </div>
            </div>
            
            <h3>Proof Obligations</h3>
            <div class="progress-bar">
                <div class="progress-fill" style="width: {self._calculate_proof_percentage(stats)}%"></div>
            </div>
            <p>{stats.get('total_proven', 0)} / {stats.get('total_proof_obligations', 0)} proof obligations proven ({self._calculate_proof_percentage(stats):.1f}%)</p>
            
            <h3>Specifications (Dafny → ACSL)</h3>
            <table>
                <tr>
                    <th>Type</th>
                    <th>Dafny</th>
                    <th>ACSL</th>
                </tr>
                <tr>
                    <td>Requires (Preconditions)</td>
                    <td>{stats.get('total_dafny_requires', 0)}</td>
                    <td>{stats.get('total_acsl_requires', 0)}</td>
                </tr>
                <tr>
                    <td>Ensures (Postconditions)</td>
                    <td>{stats.get('total_dafny_ensures', 0)}</td>
                    <td>{stats.get('total_acsl_ensures', 0)}</td>
                </tr>
                <tr>
                    <td>Loop Invariants</td>
                    <td>{stats.get('total_dafny_invariant', 0)}</td>
                    <td>{stats.get('total_acsl_invariant', 0)}</td>
                </tr>
                <tr>
                    <td>Decreases</td>
                    <td>{stats.get('total_dafny_decreases', 0)}</td>
                    <td>-</td>
                </tr>
                <tr>
                    <td>Modifies</td>
                    <td>{stats.get('total_dafny_modifies', 0)}</td>
                    <td>-</td>
                </tr>
            </table>
        </div>
        """
    
    def _calculate_proof_percentage(self, stats: Dict[str, Any]) -> float:
        total = stats.get('total_proof_obligations', 0)
        proven = stats.get('total_proven', 0)
        if total == 0:
            return 0
        return (proven / total) * 100
    
    def _generate_programs_table(self, programs: List[Dict[str, Any]]) -> str:
        if not programs:
            return "<p>No programs processed yet.</p>"
        
        rows = ""
        for prog in programs:
            status = self._get_status_badge(prog)
            dafny_specs = f"R:{prog.get('dafny_requires', 0)} E:{prog.get('dafny_ensures', 0)} I:{prog.get('dafny_invariant', 0)}"
            acsl_specs = f"R:{prog.get('precondition_count', 0)} E:{prog.get('postcondition_count', 0)} I:{prog.get('invariant_count', 0)}"
            rows += f"""
            <tr>
                <td>{prog.get('program_id', 'N/A')}</td>
                <td>{prog.get('source_language', 'N/A')} → {prog.get('target_language', 'N/A')}</td>
                <td>{dafny_specs}</td>
                <td>{acsl_specs}</td>
                <td>{prog.get('proof_obligations', 0)}</td>
                <td>{prog.get('proven_obligations', 0)}</td>
                <td>{'Y' if prog.get('compiles') else 'N'}</td>
                <td>{'Y' if prog.get('verified') else 'N'}</td>
                <td>{self._roundtrip_badge(prog)}</td>
                <td>{self._mutation_badge(prog)}</td>
                <td>{status}</td>
            </tr>
            """
        
        return f"""
        <table>
            <thead>
                <tr>
                    <th>Program ID</th>
                    <th>Translation</th>
                    <th>Dafny Specs</th>
                    <th>ACSL Specs</th>
                    <th>Proof Obl.</th>
                    <th>Proven</th>
                    <th>Compiles</th>
                    <th>Verified</th>
                    <th>Round-trip</th>
                    <th>Mutation</th>
                    <th>Status</th>
                </tr>
            </thead>
            <tbody>
                {rows}
            </tbody>
        </table>
        """
    
    def _generate_code_comparison(self, programs: List[Dict[str, Any]]) -> str:
        if not programs:
            return "<p>No programs to compare.</p>"
        
        import html
        rows = ""
        for prog in programs:
            pid = prog.get('program_id', 'unknown')
            dafny_code = html.escape(prog.get('source_code', ''))
            acsl_code = html.escape(prog.get('target_code', ''))
            
            rows += f"""
            <div class="code-compare-item" style="margin-bottom: 30px;">
                <h3 style="margin-bottom: 10px;">{pid}</h3>
                <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 15px;">
                    <div>
                        <h4 style="color: #667eea; margin-bottom: 5px;">Dafny (Source)</h4>
                        <pre class="code-block" style="max-height: 400px;">{dafny_code or 'N/A'}</pre>
                    </div>
                    <div>
                        <h4 style="color: #38ef7d; margin-bottom: 5px;">ACSL (Target)</h4>
                        <pre><code class="language-c code-block" style="max-height: 400px;">{acsl_code or 'N/A'}</code></pre>
                    </div>
                </div>
            </div>
            """
        
        return f"""
        <div class="code-compare-list">
            {rows}
        </div>
        """
    
    def _get_status_badge(self, prog: Dict[str, Any]) -> str:
        if prog.get('verified'):
            return '<span class="status success">Verified</span>'
        elif prog.get('compiles'):
            return '<span class="status pending">Partial</span>'
        else:
            return '<span class="status failed">Failed</span>'

    def _mutation_badge(self, prog: Dict[str, Any]) -> str:
        mutation = prog.get('mutation_testing') or {}
        status = mutation.get('status', '')
        if status == 'passed':
            return '<span class="status success">Passed</span>'
        if status == 'failed':
            return '<span class="status failed">Failed</span>'
        if status == 'skipped':
            return '<span class="status pending">Skipped</span>'
        return '<span class="status pending">N/A</span>'

    def _roundtrip_badge(self, prog: Dict[str, Any]) -> str:
        roundtrip = prog.get('roundtrip') or {}
        status = roundtrip.get('status', '')
        if status == 'passed':
            return '<span class="status success">Passed</span>'
        if status == 'failed':
            return '<span class="status failed">Failed</span>'
        if status == 'skipped':
            return '<span class="status pending">Skipped</span>'
        return '<span class="status pending">N/A</span>'
    
    def _generate_errors_section(self, errors: List[Dict[str, Any]]) -> str:
        if not errors:
            return ""
        
        error_items = ""
        for err in errors:
            error_items += f"""
            <div class="error-item">
                <strong>{err.get('program_id', 'Unknown')}</strong>: {err.get('message', '')}
                <br><small>{err.get('timestamp', '')}</small>
            </div>
            """
        
        return f"""
        <div class="card error-list">
            <h2>Errors ({len(errors)})</h2>
            {error_items}
        </div>
        """


def generate_translation_report(programs: List[Dict[str, Any]], output_path: str = "output/translation_report.md"):
    """Generate a markdown report for manual ACSL updates."""
    
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    
    content = "# Translation Report\n\n"
    content += "This report lists all translated files that may need manual review for ACSL specifications.\n\n"
    content += "## Summary\n\n"
    content += f"- Total programs: {len(programs)}\n"
    content += f"- Compiled: {sum(1 for p in programs if p.get('compiles'))}\n"
    content += f"- Verified: {sum(1 for p in programs if p.get('verified'))}\n\n"
    
    content += "## Files Requiring Manual Review\n\n"
    content += "| Program ID | Source | Target | Compiles | Verified | Notes |\n"
    content += "|------------|--------|--------|----------|----------|-------|\n"
    
    for prog in programs:
        compiles = "Y" if prog.get('compiles') else "N"
        verified = "Y" if prog.get('verified') else "N"
        notes = ""
        
        if not prog.get('compiles'):
            notes = "Compilation failed"
        elif not prog.get('verified'):
            notes = "Needs manual ACSL review"
        
        content += f"| {prog.get('program_id', 'N/A')} | {prog.get('source_language', '')} | {prog.get('target_language', '')} | {compiles} | {verified} | {notes} |\n"
    
    content += "\n## Detailed Information\n\n"
    
    for prog in programs:
        content += f"### {prog.get('program_id', 'Unknown')}\n\n"
        content += f"- Source Language: {prog.get('source_language', 'N/A')}\n"
        content += f"- Target Language: {prog.get('target_language', 'N/A')}\n"
        content += f"- Specifications: {prog.get('specification_count', 0)}\n"
        content += f"- Preconditions: {prog.get('precondition_count', 0)}\n"
        content += f"- Postconditions: {prog.get('postcondition_count', 0)}\n"
        content += f"- Loop Invariants: {prog.get('invariant_count', 0)}\n"
        content += f"- Compilation: {'Success' if prog.get('compiles') else 'Failed'}\n"
        content += f"- Verification: {'Success' if prog.get('verified') else 'Failed'}\n"
        content += f"- Round-trip: {(prog.get('roundtrip') or {}).get('status', 'N/A')}\n"
        content += f"- Mutation Testing: {(prog.get('mutation_testing') or {}).get('status', 'N/A')}\n"
        content += f"- Proof Obligations: {prog.get('proof_obligations', 0)}\n"
        content += f"- Proven: {prog.get('proven_obligations', 0)}\n\n"
        
        if prog.get('compilation_errors'):
            content += "#### Compilation Errors\n"
            for err in prog.get('compilation_errors', []):
                content += f"- {err}\n"
            content += "\n"
    
    with open(output_path, 'w') as f:
        f.write(content)
    
    return output_path
