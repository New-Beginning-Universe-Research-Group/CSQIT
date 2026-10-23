#!/bin/bash
export GIT_PAGER=cat
cd /mnt/d/CSQIT-W1
rm -f full_compile.sh
git add -A
git commit -m "compile-verified snapshot: single BOM across tex/lean, lake 2057 jobs 0 errors, EN 13pp / ZH 14pp 0 errors, stats 9825 synced by author" >/dev/null 2>&1
echo "head: $(git rev-parse --short HEAD)"
L=$(git rev-parse HEAD)
R=$(git ls-remote origin refs/heads/master | cut -c1-40)
if [ "$L" != "$R" ]; then
  for i in 1 2 3 4 5 6 7 8; do
    if git push origin master >/tmp/p.log 2>&1; then echo "PUSH_OK"; break; fi
    tail -1 /tmp/p.log; sleep 8
  done
else
  echo "ALREADY_SYNCED"
fi
echo "remote_head: $(git ls-remote origin refs/heads/master | cut -c1-7)"