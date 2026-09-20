$files = @(
    'V12/Core/Foundation.lean',
    'V12/Core/AxiomDerivation.lean',
    'V12/Core/Fin7Uniqueness.lean',
    'V12/Core/AlgebraicTimeCircle.lean',
    'V12/Core/QuantumTimeCircle.lean',
    'V12/Core/GravitationalAnomaly.lean',
    'V12/Core/CSQITWeaver.lean',
    'V12/Core/ErrorBounds.lean',
    'V12/Core/TopologicalTime.lean',
    'V12/Unified/Models/AxionDarkEnergyCoupled.lean'
)

$output = "V12_all_modules_v12.1.5_2026-08-06-1530.txt"
$sb = New-Object System.Text.StringBuilder

[void]$sb.AppendLine("# V12 终极编译器 - 全部模块源代码")
[void]$sb.AppendLine("# 导出时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')")
[void]$sb.AppendLine("# 版本: v12.1.5")
[void]$sb.AppendLine("# 模块数量: $($files.Count)")

$totalLines = 0
foreach ($f in $files) {
    $fullPath = "d:\CSQIT-workspace\$f"
    if (Test-Path $fullPath) {
        $lines = (Get-Content $fullPath -Encoding UTF8).Count
        $totalLines += $lines
    }
}
[void]$sb.AppendLine("# 总行数: $totalLines")
[void]$sb.AppendLine("")

foreach ($f in $files) {
    $fullPath = "d:\CSQIT-workspace\$f"
    if (Test-Path $fullPath) {
        [void]$sb.AppendLine("# ====== $f ======")
        $content = Get-Content $fullPath -Encoding UTF8 -Raw
        [void]$sb.Append($content)
        if (-not $content.EndsWith("`n")) {
            [void]$sb.AppendLine("")
        }
        [void]$sb.AppendLine("")
    }
}

[System.IO.File]::WriteAllText("d:\CSQIT-workspace\$output", $sb.ToString(), [System.Text.UTF8Encoding]::new($true))
Write-Output "Export completed: $output"
Write-Output "Total lines: $totalLines"
