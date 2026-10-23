#!/bin/bash
export GIT_PAGER=cat
cd /mnt/d/CSQIT-W1
echo "local:  $(git rev-parse --short HEAD) $(git log --oneline -1)"
L=$(git rev-parse HEAD)
R=$(git ls-remote origin refs/heads/master | cut -c1-40)
echo "remote: ${R:0:7}"
if [ "$L" != "$R" ]; then
  for i in 1 2 3 4 5; do
    if git push origin master 2>&1 | tail -1; then break; fi
    sleep 5
  done
  R2=$(git ls-remote origin refs/heads/master | cut -c1-40)
  [ "$L" = "$R2" ] && echo "SYNCED" || echo "STILL_DIVERGED"
else
  echo "ALREADY_SYNCED"
fi
rm -f final_fix_push.sh fix_bom_stats.sh rebuild_check.sh push_once.sh push_retry.sh verify_stats.sh run_build.sh verify_nonroot.sh make_release.sh _sync_all.sh push_once.sh
echo "scripts_left: $(ls *.sh 2>/dev/null | wc -l)"