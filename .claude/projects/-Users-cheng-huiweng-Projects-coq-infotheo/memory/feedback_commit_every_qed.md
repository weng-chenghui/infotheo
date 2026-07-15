---
name: feedback_commit_every_qed
description: Commit after every Qed'd lemma, no matter how small
type: feedback
---

Commit every time a lemma is proved (Qed), no matter how small.

**Why:** User wants granular git history so progress is never lost and each lemma proof is individually trackable.

**How to apply:** After each `Admitted` → `Qed` change that compiles, immediately `git add` the file and `git commit` with a message naming the lemma.
