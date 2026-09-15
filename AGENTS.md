- Avoid local variables that are used only once when the expression
  can be inlined. For example, prefer `match ← action with` over
  binding the result just to match it.
- Never patch in a change. At all times the code should be as if we
  started from its current specification and wrote as elegantly as
  possible. There is no hurry. Before making changes, clear your mind
  and think carefully about what the ideal implementation looks like,
  irrespective of what we we have. Implement that.
- Never use native_decide in proofs. Our proofs should not rely on the
  correctness of Lean's native evaluator.
