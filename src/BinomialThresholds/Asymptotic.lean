/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

Step 3d of the upper bound (arXiv:2603.29961 §2): the asymptotic assembly. Glues the
proven ingredients — `j_decomposition` (3a), `sum_aminus1_log_ge` (3b), `theta_ge` (3c) —
into the `hbig` inequality of `Upper.f_le_of_aux_sum_gt`, then chooses `Y`, `Mⱼ`, `J`.

Starts with the `Tⱼ ↔ θ` bridge: the `j`-th prime set `Pⱼ` is exactly the primes `≤ ⌊Y/j⌋`,
so `Tⱼ = ∑_{p∈Pⱼ} log p = θ(⌊Y/j⌋)` and the `theta_ge` engine applies.
-/
import Mathlib
import BinomialThresholds.Decomposition
import BinomialThresholds.ChebyshevLower

open Finset

namespace BinomialThresholds

/-- **The `Tⱼ ↔ θ` bridge (step 3d).** For `0 < j`, the prime set
`Pⱼ = primesBelow(Y+1).filter (p·j ≤ Y)` equals `{p prime : p ≤ ⌊Y/j⌋}` (the `p ≤ Y`
cap is non-binding since `⌊Y/j⌋ ≤ Y`), so `Tⱼ = ∑_{p∈Pⱼ} log p = θ(⌊Y/j⌋)`. This lets the
`theta_ge` Chebyshev engine lower-bound `Tⱼ`. -/
theorem T_eq_theta {Y j : ℕ} (hj : 0 < j) :
    ∑ p ∈ (Nat.primesBelow (Y + 1)).filter (fun p => p * j ≤ Y), Real.log p
      = Chebyshev.theta ((Y / j : ℕ) : ℝ) := by
  rw [Chebyshev.theta, Nat.floor_natCast]
  refine Finset.sum_congr (Finset.ext fun p => ?_) (fun _ _ => rfl)
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, hprime⟩, hpj⟩
    exact ⟨⟨hprime.pos, (Nat.le_div_iff_mul_le hj).mpr hpj⟩, hprime⟩
  · rintro ⟨⟨_, hpdiv⟩, hprime⟩
    refine ⟨⟨?_, hprime⟩, (Nat.le_div_iff_mul_le hj).mp hpdiv⟩
    have : Y / j ≤ Y := Nat.div_le_self Y j
    omega

/-- **Per-`j` bound in θ form (step 3d).** Substituting the `Tⱼ ↔ θ` bridge into the 3b
aggregation `sum_aminus1_log_ge`: for `0 < n`, `0 < j`, and any cutoff `M`,
`M·θ(⌊Y/j⌋) − log(n+M)·∑_{A<M}A − θ(⌊Y/j⌋) ≤ ∑_{p∈Pⱼ}(aₚ−1)log p`. The `theta_ge`
Chebyshev engine then lower-bounds the `θ(⌊Y/j⌋)` factor (still general `M`). -/
theorem per_j_bound {n Y j M : ℕ} (hn : 0 < n) (hj : 0 < j) :
    (M : ℝ) * Chebyshev.theta ((Y / j : ℕ) : ℝ)
        - Real.log ((n : ℝ) + M) * (∑ A ∈ Finset.range M, (A : ℝ))
        - Chebyshev.theta ((Y / j : ℕ) : ℝ)
      ≤ ∑ p ∈ (Nat.primesBelow (Y + 1)).filter (fun p => p * j ≤ Y),
          ((p - 1 - n % p : ℕ) : ℝ) * Real.log p := by
  have hP : ∀ p ∈ (Nat.primesBelow (Y + 1)).filter (fun p => p * j ≤ Y), p.Prime :=
    fun p hp => Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter _ hp)
  have h := sum_aminus1_log_ge ((Nat.primesBelow (Y + 1)).filter (fun p => p * j ≤ Y)) n M hn hP
  rwa [T_eq_theta hj] at h

/-- **Aggregated lower bound (step 3d).** Summing `per_j_bound` over `j ∈ [2,J]` (with any
per-`j` cutoff `Mⱼ = Mf j`) and chaining through the `j_decomposition` (3a), the explicit
θ/log sum bounds the `hbig` summand of `Upper.f_le_of_aux_sum_gt` from below. This reduces
the entire upper bound to a pure inequality `2·Y·log n < (this explicit sum)` — no primes,
no `f`, just θ and `log`. The remaining asymptotic grind chooses `Mf`, `Y`, `J`. -/
theorem sum_lower_le_aux {n Y J : ℕ} (Mf : ℕ → ℕ) (hn : 0 < n) :
    ∑ j ∈ Finset.Icc 2 J,
        ((Mf j : ℝ) * Chebyshev.theta ((Y / j : ℕ) : ℝ)
          - Real.log ((n : ℝ) + Mf j) * (∑ A ∈ Finset.range (Mf j), (A : ℝ))
          - Chebyshev.theta ((Y / j : ℕ) : ℝ))
      ≤ ∑ p ∈ Nat.primesBelow (Y + 1),
          ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p := by
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) j_decomposition
  rw [Finset.mem_Icc] at hj
  exact per_j_bound hn (by omega)

end BinomialThresholds
