Make sure one proof line one tactic and lemma.
Insert `Show` after each proof line to read the actual goal and context.
Use `apply` and `exact` instead of `apply:` and `exact:` to get more information.
Use explicit application `@lemma ...` to make sure you have the right arguments.
Remove modified files' `.vo` object files, then `make` them to verify your changes work well.
For dependent type errors, first try to make types explicits instead letting Coq infers;
if not working, split to helper lemmas no matter how small they are -- if it works then inline them back with proper explicit typing.
For Hypothesis, Abort, Admitted, you should report to the user.
For specific issue you repeatedly debug with, create a inline Coq file by `cat >> ... << EOF` and call coqc to test issue specifically.
