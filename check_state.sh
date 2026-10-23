#!/bin/bash
export GIT_PAGER=cat
cd /mnt/d/CSQIT-W1
git log --oneline -1
git ls-remote origin refs/heads/master | cut -c1-7
ls *.sh 2>/dev/null | wc -l