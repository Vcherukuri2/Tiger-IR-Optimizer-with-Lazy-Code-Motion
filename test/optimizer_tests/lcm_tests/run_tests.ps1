<#
.SYNOPSIS
  Run the lcm_tests suite. For each test directory under this folder:

    1. Interpret the original .ir file (baseline) using the project's
       IRInterpreter, capturing stdout AND the trailing "Number of
       non-label instructions executed: N" stats line on stderr.
    2. Run the optimizer (Demo) on the same .ir, honoring the contents
       of `passes.txt` for that test (an empty file means run the full
       default pipeline).
    3. Interpret the produced .opt.ir.
    4. Assert: optimized stdout == baseline stdout (semantic correctness)
       AND optimized executed-instr-count <= baseline (no regression).
    5. If an `<name>.expected.ir` file exists in the test directory,
       additionally diff it textually against the optimizer's output
       (informational only — mismatch warns, doesn't fail the test).

  Exits 0 iff every test passes both assertions.

.PARAMETER Build
  Force-rebuild the optimizer (`build/optimizer`) before running.

.EXAMPLE
  pwsh -File test/optimizer_tests/lcm_tests/run_tests.ps1
#>
param(
    [switch]$Build,
    [switch]$KeepArtifacts
)

$ErrorActionPreference = 'Stop'
$projectRoot = Resolve-Path (Join-Path $PSScriptRoot '..\..\..')
$testRoot    = $PSScriptRoot
$buildDir    = Join-Path $projectRoot 'build\optimizer'

function Build-Optimizer {
    Write-Host '[build] javac src/optimizer ...'
    New-Item -ItemType Directory -Force -Path $buildDir | Out-Null
    Push-Location $projectRoot
    try {
        $srcs = @(
            'src/optimizer/ir/*.java',
            'src/optimizer/ir/datatype/*.java',
            'src/optimizer/ir/operand/*.java',
            'src/optimizer/middle_end/*.java',
            'src/optimizer/*.java'
        )
        # javac on Windows accepts forward slashes in paths.
        & javac @srcs -d $buildDir
        if ($LASTEXITCODE -ne 0) { throw "javac failed (exit $LASTEXITCODE)" }
    } finally {
        Pop-Location
    }
}

if ($Build -or -not (Test-Path (Join-Path $buildDir 'Demo.class'))) {
    Build-Optimizer
}

function Get-ExecutedCount {
    param([string]$StderrText)
    $m = [regex]::Match($StderrText, 'Number of non-label instructions executed:\s*(\d+)')
    if (-not $m.Success) { return $null }
    return [int]$m.Groups[1].Value
}

function Get-OperationCount {
    param([string]$StderrText)
    # Prefer the explicit "Operation count" line emitted by IRInterpreter (excludes
    # LABEL and ASSIGN — the standard PRE / LCM accounting). Fall back to the gross
    # non-label count if running against an older build that doesn't emit it.
    $m = [regex]::Match($StderrText, 'Operation count \(excludes LABEL and ASSIGN\):\s*(\d+)')
    if ($m.Success) { return [int]$m.Groups[1].Value }
    return (Get-ExecutedCount $StderrText)
}

function Get-OpcodeLine {
    param([string]$StderrText)
    $m = [regex]::Match($StderrText, 'Per-opcode counts:.*')
    if ($m.Success) { return $m.Value.Trim() }
    return ''
}

function Run-Interpreter {
    param([string]$IrPath, [string]$StdinPath)
    # Force ASCII-clean redirection. Use Start-Process so we can pipe stdin from a file
    # without PowerShell's pipeline rewriting the bytes.
    $stdoutFile = [System.IO.Path]::GetTempFileName()
    $stderrFile = [System.IO.Path]::GetTempFileName()
    try {
        $psi = New-Object System.Diagnostics.ProcessStartInfo
        $psi.FileName = 'java'
        $psi.Arguments = "-cp `"$buildDir`" IRInterpreter `"$IrPath`""
        $psi.UseShellExecute = $false
        $psi.RedirectStandardInput  = $true
        $psi.RedirectStandardOutput = $true
        $psi.RedirectStandardError  = $true
        $proc = [System.Diagnostics.Process]::Start($psi)
        if (Test-Path $StdinPath) {
            $proc.StandardInput.Write([System.IO.File]::ReadAllText($StdinPath))
        }
        $proc.StandardInput.Close()
        $stdoutTask = $proc.StandardOutput.ReadToEndAsync()
        $stderrTask = $proc.StandardError.ReadToEndAsync()
        $proc.WaitForExit()
        return [pscustomobject]@{
            ExitCode = $proc.ExitCode
            Stdout   = $stdoutTask.Result
            Stderr   = $stderrTask.Result
        }
    } finally {
        Remove-Item -ErrorAction SilentlyContinue $stdoutFile, $stderrFile
    }
}

function Run-Optimizer {
    param([string]$IrPath, [string]$OutIrPath, [string]$Passes)
    # Don't shadow PowerShell's automatic $args; use $cliArgs instead.
    $cliArgs = @('-cp', $buildDir, 'Demo')
    if ($Passes -and $Passes.Trim().Length -gt 0) {
        $cliArgs += @('-passes', $Passes.Trim())
    }
    $cliArgs += @($IrPath, $OutIrPath)
    $stdoutFile = [System.IO.Path]::GetTempFileName()
    $stderrFile = [System.IO.Path]::GetTempFileName()
    try {
        $p = Start-Process -FilePath 'java' -ArgumentList $cliArgs `
            -RedirectStandardOutput $stdoutFile -RedirectStandardError $stderrFile `
            -NoNewWindow -PassThru -Wait
        return [pscustomobject]@{
            ExitCode = $p.ExitCode
            Stdout   = [System.IO.File]::ReadAllText($stdoutFile)
            Stderr   = [System.IO.File]::ReadAllText($stderrFile)
        }
    } finally {
        Remove-Item -ErrorAction SilentlyContinue $stdoutFile, $stderrFile
    }
}

$tests = Get-ChildItem -Path $testRoot -Directory | Sort-Object Name
$passCount = 0
$failCount = 0
$summary = @()

foreach ($testDir in $tests) {
    $name = $testDir.Name
    $ir   = Join-Path $testDir.FullName "$name.ir"
    if (-not (Test-Path $ir)) {
        # Convention: only directories with a matching <name>.ir are tests.
        continue
    }
    $inFile     = Join-Path $testDir.FullName "$name.in"
    $passesFile = Join-Path $testDir.FullName 'passes.txt'
    $optIr      = Join-Path $testDir.FullName "$name.opt.ir"
    $expectedIr = Join-Path $testDir.FullName "$name.expected.ir"

    $passes = ''
    if (Test-Path $passesFile) {
        $passes = (Get-Content $passesFile -Raw).Trim()
    }

    Write-Host ''
    Write-Host "==== $name ====" -ForegroundColor Cyan
    Write-Host "  passes : $(if ($passes) { $passes } else { '<full pipeline>' })"

    $baseline = Run-Interpreter -IrPath $ir -StdinPath $inFile
    if ($baseline.ExitCode -ne 0) {
        Write-Host "  [FAIL] baseline interpreter exited $($baseline.ExitCode)" -ForegroundColor Red
        Write-Host $baseline.Stderr
        $failCount++; $summary += "FAIL  $name (baseline interp)"; continue
    }
    $baselineCount  = Get-ExecutedCount  $baseline.Stderr
    $baselineOps    = Get-OperationCount $baseline.Stderr
    $baselineOpcode = Get-OpcodeLine     $baseline.Stderr
    Write-Host "  base   : $baselineCount instructions ($baselineOps ops; ASSIGN+LABEL excluded)"

    $opt = Run-Optimizer -IrPath $ir -OutIrPath $optIr -Passes $passes
    if ($opt.ExitCode -ne 0) {
        Write-Host "  [FAIL] Demo exited $($opt.ExitCode)" -ForegroundColor Red
        Write-Host $opt.Stderr
        $failCount++; $summary += "FAIL  $name (optimizer)"; continue
    }

    $optimized = Run-Interpreter -IrPath $optIr -StdinPath $inFile
    if ($optimized.ExitCode -ne 0) {
        Write-Host "  [FAIL] optimized interpreter exited $($optimized.ExitCode)" -ForegroundColor Red
        Write-Host $optimized.Stderr
        $failCount++; $summary += "FAIL  $name (optimized interp)"; continue
    }
    $optimizedCount  = Get-ExecutedCount  $optimized.Stderr
    $optimizedOps    = Get-OperationCount $optimized.Stderr
    $optimizedOpcode = Get-OpcodeLine     $optimized.Stderr
    Write-Host "  opt    : $optimizedCount instructions ($optimizedOps ops; ASSIGN+LABEL excluded)"

    $stdoutOk = ($baseline.Stdout -eq $optimized.Stdout)
    # Operation count (excludes ASSIGN and LABEL) is the no-regression metric — see README.md.
    $countOk  = ($null -ne $baselineOps -and $null -ne $optimizedOps -and $optimizedOps -le $baselineOps)
    $delta    = if ($null -ne $baselineOps -and $null -ne $optimizedOps) { $baselineOps - $optimizedOps } else { '?' }

    if (-not $stdoutOk) {
        Write-Host "  [FAIL] stdout differs (semantic regression)" -ForegroundColor Red
        Write-Host "    baseline : $($baseline.Stdout)"
        Write-Host "    optimized: $($optimized.Stdout)"
        Write-Host "  baseline opcode counts : $baselineOpcode"
        Write-Host "  optimized opcode counts: $optimizedOpcode"
        $failCount++; $summary += "FAIL  $name (stdout differs)"; continue
    }
    if (-not $countOk) {
        Write-Host "  [FAIL] optimized executes MORE operations than baseline (regression)" -ForegroundColor Red
        Write-Host "    baseline_ops=$baselineOps, optimized_ops=$optimizedOps"
        Write-Host "  baseline opcode counts : $baselineOpcode"
        Write-Host "  optimized opcode counts: $optimizedOpcode"
        Write-Host "  optimized IR kept at: $optIr"
        $failCount++; $summary += "FAIL  $name (perf regression)"; continue
    }

    if (Test-Path $expectedIr) {
        $expectedText = (Get-Content $expectedIr -Raw) -replace "`r`n", "`n"
        $actualText   = (Get-Content $optIr      -Raw) -replace "`r`n", "`n"
        if ($expectedText.TrimEnd() -ne $actualText.TrimEnd()) {
            Write-Host "  [warn] optimizer output does NOT match expected.ir textually" -ForegroundColor Yellow
            Write-Host "         (passes semantic + count checks; expected.ir is informational)"
        } else {
            Write-Host "  expected.ir matches exactly" -ForegroundColor Green
        }
    }

    Write-Host "  [PASS] saved $delta operations; stdout matches" -ForegroundColor Green
    $passCount++
    $summary += "PASS  $name (saved $delta ops)"

    if (-not $KeepArtifacts) {
        Remove-Item -ErrorAction SilentlyContinue $optIr
    }
}

# Don't auto-clean .opt.ir files for tests that FAILED — leave them for debugging.

Write-Host ''
Write-Host '==== SUMMARY ====' -ForegroundColor Cyan
$summary | ForEach-Object { Write-Host "  $_" }
Write-Host "  $passCount passed, $failCount failed"
exit ([int]($failCount -gt 0))
