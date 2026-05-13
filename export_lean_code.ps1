$outputPath = 'D:\CSQIT\all_lean_code.txt'

if (Test-Path $outputPath) {
    Remove-Item $outputPath
}

Get-ChildItem -Path 'D:\CSQIT' -Recurse -Filter '*.lean' | ForEach-Object {
    $fileContent = Get-Content -Path $_.FullName -Raw -Encoding UTF8
    
    $header = @"
================================================================================
File: $($_.FullName)
Last Modified: $($_.LastWriteTime)
Size: $($_.Length) bytes
================================================================================

"@
    
    [System.IO.File]::AppendAllText($outputPath, $header, [System.Text.Encoding]::UTF8)
    [System.IO.File]::AppendAllText($outputPath, $fileContent, [System.Text.Encoding]::UTF8)
    [System.IO.File]::AppendAllText($outputPath, "`r`n`r`n", [System.Text.Encoding]::UTF8)
}

Write-Host "Successfully exported all Lean code to $outputPath"