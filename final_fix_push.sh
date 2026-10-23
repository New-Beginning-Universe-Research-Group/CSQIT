#!/bin/bash
cd /mnt/d/CSQIT-W1/paper
pdflatex -interaction=nonstopmode csqit_w1_paper.tex >/dev/null 2>&1
pdflatex -interaction=nonstopmode csqit_w1_paper.tex >/dev/null 2>&1
echo "EN: $(grep -c '^!' csqit_w1_paper.log) errors | $(grep -c 'Overfull' csqit_w1_paper.log) overfull"
grep 'Overfull' csqit_w1_paper.log | grep -oP '\(\d+\.\d+pt' | sort -rn | head -5
cd /mnt/d/CSQIT-W1
export GIT_PAGER=cat
git add CSQIT_W1/TheoryFoundations.lean paper/csqit_w1_paper.tex paper/csqit_w1_paper_zh.tex paper/csqit_w1_paper.pdf paper/csqit_w1_paper_zh.pdf paper/cover_letter.txt
git commit -m "fix: single BOM in TheoryFoundations, 9824->9825 line count (5x), sloppy-wrap URL and Key-modules paragraphs to kill overflow" >/dev/null
git push origin master 2>&1 | tail -1
git log --oneline -1