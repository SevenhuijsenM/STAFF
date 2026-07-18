param(
  [Parameter(Mandatory = $true)]
  [string]$Dataset,
  [string]$Model = "gpt-5.5",
  [double]$Temperature = 1.0,
  [int]$MaxVerifyIters = 1,
  [string]$RunLabel = "",
  [string]$DafnyExecutable = "dafny"
)

$ErrorActionPreference = "Stop"

if (-not $env:OPENAI_API_KEY) {
  Write-Error "OPENAI_API_KEY is not set"
}

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $ScriptDir

if (-not $RunLabel) {
  $modelSlug = $Model.Replace('.', '-').Replace('/', '-')
  $RunLabel = "$Dataset-$modelSlug-reverse-$(Get-Date -Format 'yyyyMMdd-HHmmss')"
}

python formalspecc_skill.py run `
  --dataset "$Dataset" `
  --output-root "runs-reverse" `
  --output-folder "$RunLabel" `
  --model "$Model" `
  --temperature "$Temperature" `
  --max-verify-iters "$MaxVerifyIters" `
  --checkpoint-every 10 `
  --source-lang "acsl" `
  --target-lang "dafny" `
  --dafny-executable "$DafnyExecutable"

$runDir = "runs-reverse/$RunLabel"
python formalspecc_skill.py all `
  --dataset "$RunLabel" `
  --run-dir "$runDir" `
  --out-dir "$runDir/analysis"

Write-Host ""
Write-Host "Done. Review:"
Write-Host "  $ScriptDir/$runDir/analysis/summary/summary.md"
