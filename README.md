# Conditional Lean appendix for `C_53 <= 4`

This is a conditional Lean 4 formalization of the argument giving the improved
upper bound

```text
C_53 <= 4
```

for the Davenport constant problem recorded in Terence Tao's optimization
problems repository:

https://github.com/teorth/optimizationproblems

More precisely, the formalized bound is the pointwise estimate

```text
D(C_n^3) <= 4*n - P(n) - 2,
```

where `P(n)` is the largest prime-power component of `n`.

The Lean appendix was prepared with the help of Aristotle and GPT-5.5 Pro.

## Build

```bash
lake exe cache get
lake build
```

On macOS, if `tar` reports a locale error, use:

```bash
LC_ALL=C LANG=C lake exe cache get
LC_ALL=C LANG=C lake build
```
