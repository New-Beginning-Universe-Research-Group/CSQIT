$outputPath = 'D:\CSQIT\all_docs.txt'

if (Test-Path $outputPath) {
    Remove-Item $outputPath
}

$docs = @(
    'D:\CSQIT\README.md',
    'D:\CSQIT\Appendices\AppendixA\README.md',
    'D:\CSQIT\Appendices\AppendixB\README.md',
    'D:\CSQIT\Appendices\AppendixC\README.md',
    'D:\CSQIT\Appendices\AppendixD\README.md',
    'D:\CSQIT\Appendices\AppendixE\README.md',
    'D:\CSQIT\Appendices\AppendixF\README.md',
    'D:\CSQIT\Appendices\AppendixG\README.md',
    'D:\CSQIT\Appendices\AppendixH\README.md',
    'D:\CSQIT\Appendices\AppendixI\README.md',
    'D:\CSQIT\Appendices\AppendixJ\README.md',
    'D:\CSQIT\Appendices\AppendixK\README.md',
    'D:\CSQIT\Appendices\AppendixL\README.md',
    'D:\CSQIT\Appendices\AppendixN\README.md'
)

$hdstDocs = Get-ChildItem -Path 'D:\' -Recurse -Filter '*HDST*' -ErrorAction SilentlyContinue | Where-Object { $_.Extension -eq '.md' }

foreach ($doc in $hdstDocs) {
    $docs += $doc.FullName
}

foreach ($doc in $docs) {
    if (Test-Path $doc) {
        $fileContent = Get-Content -Path $doc -Raw -Encoding UTF8
        
        $header = @"
================================================================================
File: $doc
Size: $(Get-Item $doc).Length bytes
================================================================================

"@
        
        [System.IO.File]::AppendAllText($outputPath, $header, [System.Text.Encoding]::UTF8)
        [System.IO.File]::AppendAllText($outputPath, $fileContent, [System.Text.Encoding]::UTF8)
        [System.IO.File]::AppendAllText($outputPath, "`r`n`r`n", [System.Text.Encoding]::UTF8)
    } else {
        Write-Host "File not found: $doc"
    }
}

Write-Host "Successfully exported all documents to $outputPath"