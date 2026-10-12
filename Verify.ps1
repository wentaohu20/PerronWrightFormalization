param(
    [switch] $FullAudit,
    [switch] $SkipCache
)

$ErrorActionPreference = 'Stop'
# Native Lean/Lake output is UTF-8, including when Windows PowerShell 5 is used.
$utf8 = New-Object System.Text.UTF8Encoding($false)
$OutputEncoding = $utf8
[Console]::InputEncoding = $utf8
[Console]::OutputEncoding = $utf8
$project = $PSScriptRoot
$reports = Join-Path $project '.verification'

function Invoke-Checked {
    param([string] $Label, [scriptblock] $Command, [string] $Log)
    Write-Host "`n=== $Label ==="
    $output = @()
    $failure = $null
    $previousPreference = $ErrorActionPreference
    $PSNativeCommandUseErrorActionPreference = $false
    $global:LASTEXITCODE = 0
    try {
        # Windows PowerShell 5 wraps native stderr as ErrorRecord objects.
        # Capture it without terminating before the log can be written.
        $ErrorActionPreference = 'Continue'
        $output = @(& $Command 2>&1)
    } catch {
        $failure = $_
        $output += $_
    } finally {
        $ErrorActionPreference = $previousPreference
    }
    $code = $global:LASTEXITCODE
    $text = @($output | ForEach-Object { $_.ToString() })
    [IO.File]::WriteAllLines($Log, [string[]]$text, $utf8)
    $scriptErrors = @($output | Where-Object {
        $_ -is [System.Management.Automation.ErrorRecord] -and
        $_.FullyQualifiedErrorId -notlike 'NativeCommandError*'
    })
    if ($null -ne $failure -or $scriptErrors.Count) {
        throw "$Label failed; see $Log"
    }
    if ($code -ne 0) { throw "$Label failed (exit $code); see $Log" }
    if (@($text | Where-Object { $_ -match '(?i)\b(error|warning)(\([^)]*\))?:' }).Count) {
        throw "$Label emitted a diagnostic; see $Log"
    }
    Write-Host "OK (full output saved to $Log)"
}

Push-Location -LiteralPath $project
try {
    if (!(Get-Command lake -ErrorAction SilentlyContinue)) {
        throw 'Lake/Elan is required. Install Lean via https://lean-lang.org/install/ and run this entry again.'
    }
    New-Item -ItemType Directory -Force -Path $reports | Out-Null
    $files = @(Get-ChildItem -LiteralPath (Join-Path $project 'PerronWright') -Recurse -File -Filter '*.lean')
    $pattern = '(?m)^\s*(?:(?:private|protected)\s+)?(?:axiom|unsafe|opaque|sorry|admit)\b|:=\s*(?:sorry|admit)\b|skipKernelTC|sorryAx'
    foreach ($file in $files) {
        if ((Get-Content -Raw -Encoding UTF8 -LiteralPath $file.FullName) -match $pattern) {
            throw "Forbidden proof placeholder or kernel bypass in $($file.FullName)"
        }
    }
    if (!$SkipCache) {
        Invoke-Checked 'Fetch pinned mathlib cache' { lake exe cache get } (Join-Path $reports 'cache.log')
    }
    Invoke-Checked 'Build all project proof modules' { & ./Build.ps1 PerronWright } (Join-Path $reports 'build.log')
    # Never accept a stale report after a failed dependency traversal.
    $jsonPath = Join-Path $reports 'main-theorem-dependencies.json'
    $axiomsPath = Join-Path $reports 'main-theorem-axioms.txt'
    foreach ($path in @($jsonPath, $axiomsPath)) {
        if (Test-Path -LiteralPath $path) { Remove-Item -LiteralPath $path }
    }
    Invoke-Checked 'Check the four main-theorem groups and export dependencies' {
        lake env lean MainTheoremDependencies.lean
    } (Join-Path $reports 'main-theorem-dependencies.log')
    if (!(Test-Path -LiteralPath $jsonPath)) { throw 'Dependency report was not generated.' }
    $report = Get-Content -Raw -Encoding UTF8 -LiteralPath $jsonPath | ConvertFrom-Json
    if ($report.schemaVersion -ne 2 -or $report.mainTheoremCount -ne 4 -or
        $report.implementationDeclarationCount -ne 17 -or $report.supportingDeclarationCount -ne 4 -or
        $report.auditedDeclarationCount -ne 21 -or @($report.theorems).Count -ne 21) {
        throw 'Expected four paper main theorems, 17 implementation declarations and four supporting declarations.'
    }
    $numbers = @($report.paperMainTheorems | ForEach-Object { $_.number })
    if (($numbers -join ',') -ne '3.6,3.8,3.9,3.10') { throw 'Incorrect paper theorem numbering.' }
    $implementationNames = @($report.paperMainTheorems | ForEach-Object { $_.declarations } | Sort-Object -Unique)
    if ($implementationNames.Count -ne 17) { throw 'Incorrect distinct implementation count.' }
    if (@($report.supportingTheorems).Count -ne 4) { throw 'Incorrect supporting result count.' }
    $allowed = @('propext', 'Classical.choice', 'Quot.sound')
    $names = @{}
    foreach ($theorem in $report.theorems) {
        if ($names.ContainsKey($theorem.name)) { throw "Duplicate theorem: $($theorem.name)" }
        $names[$theorem.name] = $true
        $expectedNumbers = @($report.paperMainTheorems | Where-Object {
            $theorem.name -in @($_.declarations)
        } | ForEach-Object { $_.number })
        if ((@($theorem.paperTheorems) -join ',') -ne ($expectedNumbers -join ',')) {
            throw "Incorrect paper mapping for $($theorem.name)"
        }
        if (!$expectedNumbers.Count -and $theorem.name -notin @($report.supportingTheorems)) {
            throw "Unclassified audited declaration: $($theorem.name)"
        }
        if (@($theorem.proofDependencies).Count -eq 0) { throw "Missing proof dependencies: $($theorem.name)" }
        foreach ($axiom in @($theorem.axioms)) {
            if ($axiom -notin $allowed) { throw "Nonstandard axiom $axiom in $($theorem.name)" }
        }
    }
    # Print only the four paper groups, taking the union across their implementations.
    $summary = @($report.paperMainTheorems | ForEach-Object {
        $group = $_
        $used = @($report.theorems | Where-Object {
            $_.name -in @($group.declarations)
        } | ForEach-Object { $_.axioms } | Sort-Object -Unique)
        $actual = @($allowed | Where-Object { $_ -in $used })
        "THEOREM $($group.number) AXIOMS: [$($actual -join ', ')]"
    })
    if (!(Test-Path -LiteralPath $axiomsPath)) { throw 'Main-theorem axiom summary was not generated.' }
    $generated = @(Get-Content -Encoding UTF8 -LiteralPath $axiomsPath)
    if (($generated -join "`n") -ne ($summary -join "`n")) {
        throw 'Main-theorem axiom summary disagrees with the checked dependency report.'
    }
    if ($FullAudit) {
        foreach ($file in @('Audit.lean','ProbabilityAudit.lean','Chapter3FiniteProcessSpatialBridgeAudit.lean')) {
            Invoke-Checked "Full axiom audit: $file" { lake env lean $file } (Join-Path $reports "$file.log")
        }
    }
    Write-Host "`nMain-theorem axiom dependencies:"
    $summary | ForEach-Object { Write-Host $_ }
    Write-Host "`nVERIFIED: paper Theorems 3.6, 3.8, 3.9 and 3.10; only standard Lean axioms."
    Write-Host "Reports: $reports"
    exit 0
} catch {
    Write-Host "`nVERIFICATION FAILED: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
} finally {
    Pop-Location
}
