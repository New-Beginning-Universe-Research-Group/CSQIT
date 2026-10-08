#!/bin/bash
SRC=/mnt/d/1_ResearchData/CSQIT/_archive/Old_Versions/v10.4.5/Verify_History/2026-04-30_CSQIT_10.4.5_VSCode_ReBuild/.lake/packages
DST=/mnt/d/CSQIT-W1/.lake/packages
for p in batteries aesop Qq plausible Cli importGraph LeanSearchClient proofwidgets; do
  echo "=== $p ==="
  rm -rf "$DST/$p"
  cp -a "$SRC/$p" "$DST/"
  n=$(find "$DST/$p/.lake/build/lib/lean/" -name "*.olean" 2>/dev/null | wc -l)
  echo "  done ($n olean)"
done
echo ALL_PACKAGES_SYNCED
