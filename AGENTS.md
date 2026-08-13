This is an ambitious, massive formalization project to record all the intermediate mathematics between Mathlib and Fermat's Last Theorem.
* Commit as you go. Use Conventional Commits-ish style.
* Keep the dependency graph chronological: each chapter may import only earlier chapters in the same book and chapters from earlier books. Never import a later chapter or a chapter from a later book.
* Codex: use timeouts of at least 30 minutes for `wait`, `wait_agent`, and `write_stdin`.
