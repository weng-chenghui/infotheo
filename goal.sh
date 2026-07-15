#!/bin/bash
# Usage: goal.sh <file> <line> [extra_tactic]
FILE="$1"
LINE="$2"
EXTRA="${3:-idtac.}"
head -n "$LINE" "$FILE" > /tmp/goal_test.v
echo "$EXTRA" >> /tmp/goal_test.v
echo "Show." >> /tmp/goal_test.v
echo "Abort." >> /tmp/goal_test.v
# Add enough closing to make it parse
echo "Abort All." >> /tmp/goal_test.v
rocq compile -R . infotheo -R pgg-smc/protocol pgg_smc /tmp/goal_test.v 2>&1 | tail -30
