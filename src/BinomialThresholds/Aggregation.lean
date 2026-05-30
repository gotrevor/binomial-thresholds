/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

The layer-cake aggregation at the heart of the upper-bound averaging (step 3 of
arXiv:2603.29961 §2). Given the crucial-observation bound `S_A ≤ A·L` (few primes
have `aₚ ≤ A`), the "energy" `∑_{p∈P} aₚ log p` is bounded below by `M·T − L·∑_{A<M} A`.

Mechanism: `aₚ = ∑_{A≥0} 1[aₚ > A]`, so `∑ aₚ log p = ∑_A (T − S_A)` (layer cake),
and `T − S_A ≥ T − A·L`.
-/
import Mathlib

open Finset

namespace BinomialThresholds

/-- **Layer-cake aggregation.** For a finite prime set `P`, with `aₚ := p − n%p` and
`S_A := ∑_{p∈P, aₚ ≤ A} log p`, if `S_A ≤ A·L` for every `A < M` (the crucial
observation), then
`M·T − L·∑_{A<M} A ≤ ∑_{p∈P} aₚ·log p`, where `T = ∑_{p∈P} log p`. -/
theorem sum_amul_log_ge (P : Finset ℕ) (n M : ℕ) (L : ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ A ∈ Finset.range M,
        ∑ p ∈ P.filter (fun p => p - n % p ≤ A), Real.log p ≤ (A : ℝ) * L) :
    (M : ℝ) * (∑ p ∈ P, Real.log p) - L * (∑ A ∈ Finset.range M, (A : ℝ))
      ≤ ∑ p ∈ P, ((p - n % p : ℕ) : ℝ) * Real.log p := by
  have hlog : ∀ p ∈ P, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hP p hp).one_lt.le)
  -- `T − S_A` is the tail sum over primes with `aₚ > A`.
  have e1 : ∀ A, (∑ p ∈ P, Real.log p) - ∑ p ∈ P.filter (fun p => p - n % p ≤ A), Real.log p
      = ∑ p ∈ P.filter (fun p => A < p - n % p), Real.log p := by
    intro A
    have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p => A < p - n % p)
      (fun p => Real.log (p : ℝ))
    have hSeq : P.filter (fun p => ¬ A < p - n % p) = P.filter (fun p => p - n % p ≤ A) :=
      Finset.filter_congr fun p _ => by rw [not_lt]
    rw [hSeq] at hsplit
    linarith [hsplit]
  -- layer cake: `∑_A (T − S_A) = ∑_p (#{A<M : A<aₚ})·log p ≤ ∑_p aₚ·log p`.
  have hlayer : ∑ A ∈ Finset.range M,
        ((∑ p ∈ P, Real.log p) - ∑ p ∈ P.filter (fun p => p - n % p ≤ A), Real.log p)
      ≤ ∑ p ∈ P, ((p - n % p : ℕ) : ℝ) * Real.log p := by
    calc ∑ A ∈ Finset.range M,
            ((∑ p ∈ P, Real.log p) - ∑ p ∈ P.filter (fun p => p - n % p ≤ A), Real.log p)
        = ∑ A ∈ Finset.range M, ∑ p ∈ P.filter (fun p => A < p - n % p), Real.log p :=
          Finset.sum_congr rfl fun A _ => e1 A
      _ = ∑ A ∈ Finset.range M, ∑ p ∈ P, if A < p - n % p then Real.log p else 0 :=
          Finset.sum_congr rfl fun A _ => by rw [Finset.sum_filter]
      _ = ∑ p ∈ P, ∑ A ∈ Finset.range M, if A < p - n % p then Real.log p else 0 :=
          Finset.sum_comm
      _ ≤ ∑ p ∈ P, ((p - n % p : ℕ) : ℝ) * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hsub : (Finset.range M).filter (fun A => A < p - n % p)
              ⊆ Finset.range (p - n % p) := fun A hA => by
            rw [Finset.mem_filter, Finset.mem_range] at hA
            exact Finset.mem_range.mpr hA.2
          have hcard : (#((Finset.range M).filter (fun A => A < p - n % p)) : ℝ)
              ≤ ((p - n % p : ℕ) : ℝ) :=
            by exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
          exact mul_le_mul_of_nonneg_right hcard (hlog p hp)
  -- assemble: `M·T − L·∑A = ∑_A (T − A·L) ≤ ∑_A (T − S_A) ≤ ∑ aₚ·log p`.
  calc (M : ℝ) * (∑ p ∈ P, Real.log p) - L * (∑ A ∈ Finset.range M, (A : ℝ))
      = ∑ A ∈ Finset.range M, ((∑ p ∈ P, Real.log p) - (A : ℝ) * L) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        · rw [← Finset.sum_mul]; ring
    _ ≤ ∑ A ∈ Finset.range M,
          ((∑ p ∈ P, Real.log p) - ∑ p ∈ P.filter (fun p => p - n % p ≤ A), Real.log p) :=
        Finset.sum_le_sum fun A hA => by linarith [hS A hA]
    _ ≤ ∑ p ∈ P, ((p - n % p : ℕ) : ℝ) * Real.log p := hlayer

end BinomialThresholds
