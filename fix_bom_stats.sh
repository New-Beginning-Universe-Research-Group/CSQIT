#!/bin/bash
cd /mnt/d/CSQIT-W1
# 1. Fix double BOM -> single BOM in TheoryFoundations.lean
python3 - <<'EOF'
p='CSQIT_W1/TheoryFoundations.lean'
b=open(p,'rb').read()
BOM=b'\xef\xbb\xbf'
while b.startswith(BOM): b=b[3:]
open(p,'wb').write(BOM+b)
print('BOM now:', open(p,'rb').read(6).hex())
EOF
# 2. 9,824 -> 9,825
sed -i 's/9,824/9,825/g' paper/csqit_w1_paper.tex paper/csqit_w1_paper_zh.tex paper/cover_letter.txt
grep -c '9,825' paper/csqit_w1_paper.tex paper/csqit_w1_paper_zh.tex paper/cover_letter.txt
# 3. Show EN URL paragraph contexts for sloppy wrap
echo "=== ctx1 ==="
grep -n -B1 -A5 'repository is available' paper/csqit_w1_paper.tex
echo "=== ctx2 ==="
grep -n -B1 -A3 'publicly available' paper/csqit_w1_paper.tex
