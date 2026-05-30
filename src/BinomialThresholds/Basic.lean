/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

Formalization of the binomial-coefficient threshold result, Section 2 of

  Alexeev, Putterman, Sawhney, Sellke, Valiant,
  "Short proofs in combinatorics and number theory",
  arXiv:2603.29961 (Apr 2026).

This answers (the order-of-growth side of) a question of Erdős on the small
prime factors of `C(n, k)` (erdosproblems.com/684).
-/
import Mathlib

open Filter Finset
open scoped BigOperators Topology

namespace BinomialThresholds

/-!
# The objects (faithful to arXiv:2603.29961 §2)

`u n k = ∏_{p ≤ k, p prime} p ^ v_p( C(n,k) )` — the part of the binomial
coefficient `C(n,k)` supported on primes `≤ k`.

`f n = min { k : u n k > n² }`.

The paper proves, for `n` large,
  `f n ≤ (24/(π²−6) + o(1)) (log n)²  ≤ 6.20219 (log n)²`,
and that `f nⱼ ≥ (1/2 + o(1)) log nⱼ` for some `nⱼ → ∞`.

## Scope decision (the "finish completely, zero axioms" line)

The paper's *sharp* constants (`24/(π²−6)`, `1/2`) come from
`θ(x) ~ x` — the Prime Number Theorem asymptotic, which is NOT in mathlib
(that is exactly what the PrimeNumberTheorem+ project exists to supply).

We deliberately formalize the **constant-relaxed** statements:
  `f n = O((log n)²)`  and  `f n = Ω(log n)` infinitely often.
These need only the *elementary* Chebyshev bounds. mathlib v4.29.1 ships the
relevant *upper* bounds (`Chebyshev.theta_le_log4_mul_x`,
`Chebyshev.psi_le_const_mul_self`, `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`)
but, as of this formalization, **no θ/ψ lower bound** — so the matching lower
bound `θ(2n) ≥ 2n·log2 − o(n)` is built from central binomials in
`BinomialThresholds.ChebyshevLower` (`theta_ge`). With that, the relaxed result
is provable unconditionally on plain mathlib v4.29.1.
-/

/-- `u n k = ∏_{p ≤ k, p prime} p ^ v_p( C(n,k) )`. -/
def u (n k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesBelow (k + 1), p ^ ((n.choose k).factorization p)

/-- `f n = min { k : u n k > n² }`. (Over `ℕ`; `sInf ∅ = 0`, so the content
of `f_le_polylog` below also certifies the witnessing set is eventually
nonempty.) -/
noncomputable def f (n : ℕ) : ℕ := sInf {k | n ^ 2 < u n k}

/-- **Upper bound** (constant-relaxed Theorem 2.1): `f n = O((log n)²)`.
Sharp constant `24/(π²−6)` would need PNT; this needs only Chebyshev. -/
theorem f_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ C * (Real.log n) ^ 2 := by
  sorry

/-- **Lower bound** (constant-relaxed): `f n ≥ c · log n` infinitely often.
Paper gives `(1/2 + o(1)) log nⱼ`; we relax to some `c > 0`.
Witness family: `n = (∏_{p ≤ K} p^{⌊log_p K⌋+1}) − 1`. -/
theorem f_ge_log_frequently :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, c * Real.log n ≤ (f n : ℝ) := by
  sorry

end BinomialThresholds
