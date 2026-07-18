param(
  [Parameter(Mandatory = $true)]
  [string]$Dataset,
  [string]$Model = "gpt-5.2",
  [double]$Temperature = 0.2,
  [int]$MaxVerifyIters = 3,
  [string]$RunLabel = "",
  [bool]$EnableDifferentialTesting = $true,
  [string]$DafnyExecutable = "dafny",
  [string]$DafnyBackend = "cpp",
  [string]$DafnyGenerateTestsMode = "InlinedBlock",
  [string]$DafnyTestBackend = "py",
  [string]$CCompiler = "gcc",
  [string]$DTestCommandTemplate = "",
  [string]$DafnyBuildCommandTemplate = "",
  [string]$DafnyGeneratedTestsCommandTemplate = "",
  [string]$TranslatedHarnessDir = "",
  [bool]$EnableMutationTesting = $true,
  [string]$MutationCommandTemplate = "acsl-mutation-tester --input {translated_c_path} --report {report_file}",
  [int]$MutationTimeout = 600,
  [string]$MutationReportName = "mutation_report.json"
)

$ErrorActionPreference = "Stop"

if (-not $env:OPENAI_API_KEY) {
  Write-Error "OPENAI_API_KEY is not set"
}

$normalizedKey = $env:OPENAI_API_KEY.Trim().ToLowerInvariant()
$placeholderMarkers = @("your_key", "your-api-key", "your_api_key", "replace_with", "sk-...", "<your")
foreach ($marker in $placeholderMarkers) {
  if ($normalizedKey.Contains($marker)) {
    Write-Error "OPENAI_API_KEY appears to be a placeholder value. Set a real API key and retry."
  }
}

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $ScriptDir

if (-not $RunLabel) {
  $modelSlug = $Model.Replace('.', '-').Replace('/', '-')
  $RunLabel = "$Dataset-$modelSlug-$(Get-Date -Format 'yyyyMMdd-HHmmss')"
}

$runArgs = @(
  "formalspecc_skill.py", "run",
  "--dataset", "$Dataset",
  "--output-root", "runs",
  "--output-folder", "$RunLabel",
  "--model", "$Model",
  "--temperature", "$Temperature",
  "--max-verify-iters", "$MaxVerifyIters",
  "--checkpoint-every", "10",
  "--dafny-executable", "$DafnyExecutable",
  "--dafny-backend", "$DafnyBackend",
  "--dafny-generate-tests-mode", "$DafnyGenerateTestsMode",
  "--dafny-test-backend", "$DafnyTestBackend",
  "--c-compiler", "$CCompiler"
)

if ($EnableDifferentialTesting) {
  $runArgs += "--enable-differential-testing"
}
if ($EnableMutationTesting) {
  $runArgs += "--enable-mutation-testing"
}
if ($DTestCommandTemplate) {
  $runArgs += @("--dtest-command-template", $DTestCommandTemplate)
}
if ($DafnyBuildCommandTemplate) {
  $runArgs += @("--dafny-build-command-template", $DafnyBuildCommandTemplate)
}
if ($DafnyGeneratedTestsCommandTemplate) {
  $runArgs += @("--dafny-generated-tests-command-template", $DafnyGeneratedTestsCommandTemplate)
}
if ($TranslatedHarnessDir) {
  $runArgs += @("--translated-harness-dir", $TranslatedHarnessDir)
}
$runArgs += @("--mutation-command-template", $MutationCommandTemplate)
$runArgs += @("--mutation-timeout", "$MutationTimeout")
if ($MutationReportName) {
  $runArgs += @("--mutation-report-name", $MutationReportName)
}

python @runArgs

$runDir = "runs/$RunLabel"
python formalspecc_skill.py all `
  --dataset "$RunLabel" `
  --run-dir "$runDir" `
  --out-dir "$runDir/analysis"

Write-Host ""
Write-Host "Done. Review:" 
Write-Host "  $ScriptDir/$runDir/analysis/summary/summary.md"
Write-Host "  $ScriptDir/$runDir/analysis/figures/status_counts.svg"
Write-Host "  $ScriptDir/$runDir/analysis/figures/proof_gap_profile.svg"
