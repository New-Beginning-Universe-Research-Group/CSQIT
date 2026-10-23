#!/bin/bash
export GIT_PAGER=cat
cd /mnt/d/CSQIT-W1
for i in 1 2 3; do
  git push origin master 2>&1 | tail -1 && break
  sleep 4
done
echo "remote_head: $(git log origin/master --oneline -1 2>/dev/null || git ls-remote origin master | cut -c1-7)"
rm -f final_fix_push.sh fix_bom_stats.sh rebuild_check.sh push_retry.sh
echo cleaned