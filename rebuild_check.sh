cd /mnt/d/CSQIT-W1/paper
pdflatex -interaction=nonstopmode csqit_w1_paper.tex >/dev/null 2>&1
pdflatex -interaction=nonstopmode csqit_w1_paper.tex >/dev/null 2>&1
xelatex -interaction=nonstopmode csqit_w1_paper_zh.tex >/dev/null 2>&1
xelatex -interaction=nonstopmode csqit_w1_paper_zh.tex >/dev/null 2>&1
echo "EN: $(grep -c '^!' csqit_w1_paper.log) errors | $(grep -c 'Overfull' csqit_w1_paper.log) overfull | $(grep -oP 'Output written.*' csqit_w1_paper.log | tail -1)"
echo "ZH: $(grep -c '^!' csqit_w1_paper_zh.log) errors | $(grep -c 'Overfull' csqit_w1_paper_zh.log) overfull | $(grep -oP 'Output written.*' csqit_w1_paper_zh.log | tail -1)"
echo "EN URL overfull left: $(grep -c 'github' <(grep 'Overfull' csqit_w1_paper.log))"
echo "ZH 9,825: $(grep -c '9,825' csqit_w1_paper_zh.tex) | EN 9,825: $(grep -c '9,825' csqit_w1_paper.tex)"