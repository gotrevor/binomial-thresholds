# Binomial Thresholds (Lean) 🔢

Formalizing **§2 of Alexeev–Putterman–Sawhney–Sellke–Valiant, "Short proofs in
combinatorics and number theory"** ([arXiv:2603.29961](https://arxiv.org/abs/2603.29961),
Apr 2026) in Lean 4 / mathlib **v4.29.1**.

Answers the order-of-growth side of an Erdős question on small prime factors of
`C(n,k)` ([erdosproblems.com/684](https://www.erdosproblems.com/684) — still
`status: open`, `formalized: no` as of this writing, so this is **new work**).

## The objects

- `u n k = ∏_{p ≤ k, p prime} p ^ v_p(C(n,k))`
- `f n = min { k : u n k > n² }`

## What we prove (and why it's fully completable)

The paper's **sharp** constants (`24/(π²−6) ≈ 6.20219` upper, `1/2` lower) come
from `θ(x) ~ x` = the **Prime Number Theorem asymptotic**, which is *not* in
mathlib (that's what PrimeNumberTheorem+ exists to supply). Importing PNT+ would
fork the mathlib cache (it's on v4.29.0) and drag a research project in as a dep.

So we deliberately target the **constant-relaxed** statements:

- `f_le_polylog`     : `f n = O((log n)²)`
- `f_ge_log_frequently` : `f n = Ω(log n)` infinitely often

These need only the **elementary Chebyshev bounds**, which mathlib v4.29.1 ships
in `Mathlib.NumberTheory.Chebyshev` (`theta_eq_sum_primesLE_log`,
`theta_le_log4_mul_x`, `two_pow_le_mul_lcmUpto`, ...). Result is unconditional,
zero axioms. (Same honest constant-relaxation move as sum-product's
`card_boxAdd_le`.) Sharp constants are optional hard-mode, gated on PNT.

## Build

```bash
cd ~/src/binomial-thresholds
lake exe cache get      # cache hit: v4.29.1 mathlib is the local standard
lake build BinomialThresholds
```

## Status

Scaffold: faithful statements of `u`, `f`, and the two relaxed theorems, both
`sorry`. Next: the upper bound (Legendre `1_{n mod p < k mod p}` + the
Chebyshev `Tⱼ` sum).

## Recording it (when proven)

Two trackers, neither hosts the proof (it lives here):
- **formal-conjectures** (DeepMind, statement DB): PR a new
  `ErdosProblems/684.lean` with the faithful statement, tag `@[category research
  open]` (684 asks for the *exact* order — bounds don't resolve it), and once
  proven add `@[formal_proof using lean4 at "<this repo URL>"]`.
- **teorth/erdosproblems** (`data/problems.yaml`): PR flipping `formalized:
  no → yes`. `status` stays `open`.

## License

[Apache License 2.0](LICENSE), Copyright 2026 Trevor Morris
