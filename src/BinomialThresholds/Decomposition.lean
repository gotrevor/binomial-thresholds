/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

Step 3a of the upper bound (arXiv:2603.29961 §2): the **j-decomposition**. The single
`(aₚ-1)·(⌊Y/p⌋-1)·log p` weight in the averaging sum is bounded below by a sum over
`j ∈ [2,J]` of contributions from the prime sets `Pⱼ = {p ≤ Y : p·j ≤ Y}`, using
`⌊Y/p⌋ - 1 ≥ #{j ∈ [2,J] : p·j ≤ Y}`. Purely combinatorial (no analysis): a Fubini
swap plus a cardinality bound. Feeds the per-`j` `R_lower` engine (steps 3b–3d).
-/
import Mathlib
import BinomialThresholds.Basic

open Finset

namespace BinomialThresholds

/-- The number of `j ∈ [2,J]` with `p·j ≤ Y` is at most `⌊Y/p⌋ - 1` (for `0 < p`):
`p·j ≤ Y ↔ j ≤ ⌊Y/p⌋` (`Nat.le_div_iff_mul_le`), so the good `j` all lie in
`Icc 2 ⌊Y/p⌋`, which has `⌊Y/p⌋ - 1` elements. -/
theorem card_filter_le {p Y J : ℕ} (hp : 0 < p) :
    #{j ∈ Finset.Icc 2 J | p * j ≤ Y} ≤ Y / p - 1 := by
  have hsub : {j ∈ Finset.Icc 2 J | p * j ≤ Y} ⊆ Finset.Icc 2 (Y / p) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    refine ⟨hj.1.1, ?_⟩
    refine (Nat.le_div_iff_mul_le hp).mpr ?_
    rw [mul_comm]; exact hj.2
  calc #{j ∈ Finset.Icc 2 J | p * j ≤ Y}
      ≤ #(Finset.Icc 2 (Y / p)) := Finset.card_le_card hsub
    _ = Y / p - 1 := by rw [Nat.card_Icc]; omega

/-- **The j-decomposition (step 3a).** For any `n Y J`, the averaging weight splits as
a lower bound over `j ∈ [2,J]`, summing the prime contributions of each `Pⱼ`:
`∑_{j=2}^J ∑_{p∈Pⱼ} (aₚ-1)·log p ≤ ∑_{p≤Y} (aₚ-1)(⌊Y/p⌋-1)·log p`, where
`Pⱼ = {p ≤ Y : p·j ≤ Y}` and `aₚ-1 = p-1-n%p`. The RHS is exactly the `hbig` summand
of `Upper.f_le_of_aux_sum_gt`. Combinatorial: Fubini swap + `card_filter_le`. -/
theorem j_decomposition {n Y J : ℕ} :
    ∑ j ∈ Finset.Icc 2 J,
        ∑ p ∈ (Nat.primesBelow (Y + 1)).filter (fun p => p * j ≤ Y),
          ((p - 1 - n % p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ Nat.primesBelow (Y + 1),
          ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p := by
  -- LHS: each inner filter-sum → indicator over the fixed set, then swap `j` and `p`,
  -- and collapse the inner `j`-sum into a cardinality.
  have hswap : ∑ j ∈ Finset.Icc 2 J,
        ∑ p ∈ (Nat.primesBelow (Y + 1)).filter (fun p => p * j ≤ Y),
          ((p - 1 - n % p : ℕ) : ℝ) * Real.log p
      = ∑ p ∈ Nat.primesBelow (Y + 1),
          ((#{j ∈ Finset.Icc 2 J | p * j ≤ Y} : ℕ) : ℝ) *
            (((p - 1 - n % p : ℕ) : ℝ) * Real.log p) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesBelow hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have hfnn : 0 ≤ ((p - 1 - n % p : ℕ) : ℝ) * Real.log p :=
    mul_nonneg (Nat.cast_nonneg _) hlog
  have hcard : ((#{j ∈ Finset.Icc 2 J | p * j ≤ Y} : ℕ) : ℝ) ≤ ((Y / p - 1 : ℕ) : ℝ) := by
    exact_mod_cast card_filter_le hpp.pos
  calc ((#{j ∈ Finset.Icc 2 J | p * j ≤ Y} : ℕ) : ℝ) *
          (((p - 1 - n % p : ℕ) : ℝ) * Real.log p)
      ≤ ((Y / p - 1 : ℕ) : ℝ) * (((p - 1 - n % p : ℕ) : ℝ) * Real.log p) :=
        mul_le_mul_of_nonneg_right hcard hfnn
    _ = ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p := by ring

end BinomialThresholds
