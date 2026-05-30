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

/-- **Double-sum swap (Fubini).** Summing the per-`k` bound over `k ∈ [1,Y]` and
swapping the order of summation, `∑_{p ≤ Y} #{k ∈ [1,Y] : p ≤ k ∧ n%p < k%p} · log p`
bounds `∑_{k=1}^Y log(u n k)` from below (needs `Y ≤ n` so every `k ≤ n`). -/
theorem sum_card_log_le_sum_log_u {n Y : ℕ} (hYn : Y ≤ n) :
    ∑ p ∈ Nat.primesBelow (Y + 1),
        ((#{k ∈ Finset.Icc 1 Y | p ≤ k ∧ n % p < k % p} : ℕ) : ℝ) * Real.log p
      ≤ ∑ k ∈ Finset.Icc 1 Y, Real.log (u n k) := by
  -- rewrite each inner prime-sum as an indicator over the fixed set `primesBelow (Y+1)`.
  have perK : ∀ k ∈ Finset.Icc 1 Y,
      ∑ p ∈ (Nat.primesBelow (k + 1)).filter (fun p => n % p < k % p), Real.log p
        = ∑ p ∈ Nat.primesBelow (Y + 1),
            if p ≤ k ∧ n % p < k % p then Real.log p else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (Finset.ext fun p => ?_) fun _ _ => rfl
    simp only [Finset.mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hpk, hpr⟩, hmod⟩; exact ⟨⟨by omega, hpr⟩, by omega, hmod⟩
    · rintro ⟨⟨_, hpr⟩, hpk, hmod⟩; exact ⟨⟨by omega, hpr⟩, hmod⟩
  -- swap, then collapse the inner `k`-sum into a cardinality.
  have key : ∑ k ∈ Finset.Icc 1 Y,
        ∑ p ∈ (Nat.primesBelow (k + 1)).filter (fun p => n % p < k % p), Real.log p
      = ∑ p ∈ Nat.primesBelow (Y + 1),
          ((#{k ∈ Finset.Icc 1 Y | p ≤ k ∧ n % p < k % p} : ℕ) : ℝ) * Real.log p := by
    rw [Finset.sum_congr rfl perK, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [← key]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  exact indicator_sum_le_log_u (le_trans hk.2 hYn)

/-- **Count lower bound, `Icc` form.** The number of `k ∈ [1,Y]` with `p ≤ k` and
`n%p < k%p` is at least `(p - 1 - n%p)·(Y/p - 1)` — the `BlockCount` bound over
`[0,Y)` minus the boundary block `[0,p)` (which holds exactly `p - 1 - n%p` such `k`).
This realizes the paper's `(aₚ - 1)(⌊Y/p⌋ - 1)`. -/
theorem card_Icc_ge {n p Y : ℕ} (hp : 0 < p) :
    (p - 1 - n % p) * (Y / p - 1) ≤ #{k ∈ Finset.Icc 1 Y | p ≤ k ∧ n % p < k % p} := by
  have ht : n % p < p := Nat.mod_lt n hp
  -- the boundary block `[0,p)` contains exactly `p - 1 - n%p` good `k` (there `k%p = k`).
  have hbnd : #{k ∈ Finset.range p | n % p < k % p} = p - 1 - n % p := by
    have hset : {k ∈ Finset.range p | n % p < k % p} = Finset.Ioo (n % p) p := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
      constructor
      · rintro ⟨hkp, hmod⟩; rw [Nat.mod_eq_of_lt hkp] at hmod; exact ⟨hmod, hkp⟩
      · rintro ⟨h1, h2⟩; rw [Nat.mod_eq_of_lt h2]; exact ⟨h2, h1⟩
    rw [hset, Nat.card_Ioo]; omega
  -- `[0,Y)` good set ⊆ (Icc good set) ∪ (boundary good set)
  have hsub : {k ∈ Finset.range Y | n % p < k % p} ⊆
      {k ∈ Finset.Icc 1 Y | p ≤ k ∧ n % p < k % p} ∪ {k ∈ Finset.range p | n % p < k % p} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rcases lt_or_ge k p with hkp | hkp
    · refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hkp, hk.2⟩
    · refine Finset.mem_union_left _ ?_
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hkp, hk.2⟩
  have hcard : #{k ∈ Finset.range Y | n % p < k % p}
      ≤ #{k ∈ Finset.Icc 1 Y | p ≤ k ∧ n % p < k % p} + (p - 1 - n % p) := by
    rw [← hbnd]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have arith : ∀ a d c : ℕ, a * d ≤ c + a → a * (d - 1) ≤ c := by
    intro a d c h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
      simp only [Nat.succ_sub_one]
      rw [Nat.mul_succ] at h
      omega
  exact arith _ _ _ (le_trans (card_filter_mod_gt hp ht) hcard)

/-- **Step 2 complete.** Combining the swap, the count bound, and `log p ≥ 0`:
`∑_{p ≤ Y} (p - 1 - n%p)(⌊Y/p⌋ - 1) log p ≤ ∑_{k=1}^Y log(u n k)` for `Y ≤ n`.
This is the lower bound on `∑ log u` that the Chebyshev averaging (step 3) divides
by `Y` and pushes past `2 log n`. -/
theorem sum_aux_le_sum_log_u {n Y : ℕ} (hYn : Y ≤ n) :
    ∑ p ∈ Nat.primesBelow (Y + 1),
        ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p
      ≤ ∑ k ∈ Finset.Icc 1 Y, Real.log (u n k) := by
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) (sum_card_log_le_sum_log_u hYn)
  have hpp := Nat.prime_of_mem_primesBelow hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  calc ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p
      = (((p - 1 - n % p) * (Y / p - 1) : ℕ) : ℝ) * Real.log p := by push_cast; ring
    _ ≤ ((#{k ∈ Finset.Icc 1 Y | p ≤ k ∧ n % p < k % p} : ℕ) : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_Icc_ge hpp.pos) hlog

end BinomialThresholds
