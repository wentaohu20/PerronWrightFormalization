param([Parameter(ValueFromRemainingArguments = $true)][string[]] $Targets)

$project = $PSScriptRoot
$packages = Join-Path $project '.lake\packages'
$repositories = @()
if (Test-Path -LiteralPath $packages) {
    $repositories = @(Get-ChildItem -LiteralPath $packages -Directory | ForEach-Object {
        $_.FullName.Replace('\', '/')
    })
}

$env:GIT_CONFIG_COUNT = [string] $repositories.Count
for ($i = 0; $i -lt $repositories.Count; $i++) {
    [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$i", 'safe.directory', 'Process')
    [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$i", $repositories[$i], 'Process')
}

Push-Location -LiteralPath $project
try {
    & lake build @Targets
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
} finally {
    Pop-Location
}
