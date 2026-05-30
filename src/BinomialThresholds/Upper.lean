/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

Assembly of the upper bound `f n = O((log n)²)` (arXiv:2603.29961 §2), built on
the three concrete cores: `Legendre`, `CrucialObs`, `BlockCount`.

This file currently holds the per-`k` bridge from the Legendre indicator to
`log (u n k)`. The remaining averaging/Chebyshev assembly is in progress.
-/
import BinomialThresholds.Basic
import BinomialThresholds.Legendre
import BinomialThresholds.CrucialObs
import BinomialThresholds.BlockCount

open Finset

namespace BinomialThresholds

/-- `log (u n k) = ∑_{p ≤ k} vₚ(C(n,k)) · log p` — unfolding the definition of `u`. -/
theorem log_u_eq (n k : ℕ) :
    Real.log (u n k) = ∑ p ∈ Nat.primesBelow (k + 1),
      ((Nat.choose n k).factorization p : ℝ) * Real.log p := by
  unfold u
  rw [Nat.cast_prod,
    Real.log_prod fun p hp =>
      Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.prime_of_mem_primesBelow hp).pos.ne')]
  exact Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]

/-- **Per-`k` lower bound.** For `k ≤ n`, the Legendre indicator sum bounds
`log (u n k)` from below: every prime `p ≤ k` with `n mod p < k mod p` contributes
at least `log p` (since then `vₚ(C(n,k)) ≥ 1`), and the other prime powers only add. -/
theorem indicator_sum_le_log_u {n k : ℕ} (hkn : k ≤ n) :
    ∑ p ∈ (Nat.primesBelow (k + 1)).filter (fun p => n % p < k % p), Real.log p
      ≤ Real.log (u n k) := by
  rw [log_u_eq]
  refine le_trans ?_
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun p => n % p < k % p) (Nat.primesBelow (k + 1))) ?_)
  · refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primesBelow hp.1
    have hind := one_le_factorization_choose hpp hkn hp.2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    calc Real.log p = 1 * Real.log p := (one_mul _).symm
      _ ≤ ((Nat.choose n k).factorization p : ℝ) * Real.log p := by
          gcongr; exact_mod_cast hind
  · intro p hp _
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    exact mul_nonneg (Nat.cast_nonneg _) hlog

end BinomialThresholds
