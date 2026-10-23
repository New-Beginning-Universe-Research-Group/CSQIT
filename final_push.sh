#!/bin/bash
export GIT_PAGER=cat
cd /mnt/d/CSQIT-W1
L=$(git rev-parse HEAD)
R=$(git ls-remote origin refs/heads/master | cut -c1-40)
if [ "$L" != "$R" ]; then
  ok=0
  for i in 1 2 3 4 5 6 7 8; do
    if git push origin master >/tmp/p.log 2>&1; then ok=1; break; fi
    tail -1 /tmp/p.log
    sleep 8
  done
  [ $ok -eq 1 ] && echo "PUSH_OK" || echo "PUSH_FAILED"
else
  echo "ALREADY_SYNCED"
fi
echo "remote_now: $(git ls-remote origin refs/heads/master | cut -c1-7)"
rm -f sync_and_clean.sh check_state.sh push_once.sh final_fix_push.sh fix_bom_stats.sh rebuild_check.sh push_retry.sh verify_stats.sh run_build.sh verify_nonroot.sh make_release.sh _sync_all.sh "$0"
ls *.sh 2>/dev/null | wc -l