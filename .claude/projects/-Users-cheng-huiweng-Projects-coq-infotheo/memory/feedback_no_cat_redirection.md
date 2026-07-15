---
name: No cat/redirection for debugging
description: Use Write and Bash tools instead of cat and redirection for debugging Coq files
type: feedback
---

When debugging Coq/Rocq files, do NOT use `cat` and shell redirection (heredoc, echo >, etc.) to create temporary test files. Instead use the Write tool for creating/editing files and Bash tool for compilation commands.
