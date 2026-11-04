#!/usr/bin/env bash
# usage: run1.sh File  (scratch compile of Lines/File.lean without writing an olean)
S=/tmp/claude-0/-home-user/4463fc2d-0ca5-5c92-8549-159b74884cf3/scratchpad; export PATH=$S/lean/tc/lean-4.31.0-linux/bin:$PATH
cd /home/user/toolchain/lean-ws && lake env bash -c "LEAN_PATH=\$LEAN_PATH:/home/user/research/difffold/proof/build-lines timeout ${T:-300} lean ${O:+-o /home/user/research/difffold/proof/build-lines/$O.olean} -DmaxHeartbeats=${HB:-1000000} --root=/home/user/research/difffold/proof/Lines /home/user/research/difffold/proof/Lines/$1.lean"
