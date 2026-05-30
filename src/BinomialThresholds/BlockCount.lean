/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

The block-counting lower bound for the upper-bound argument (arXiv:2603.29961 §2).

As `k` ranges over `[0, Y)`, the residue `k mod p` hits each class roughly `Y/p`
times. So the number of `k < Y` with `k mod p > t` is at least `(p - 1 - t)·(Y/p)`
(there are `p - 1 - t` residues in `(t, p)`, each realized ≥ `Y/p` times). With
`t = n mod p` this is `(aₚ - 1)·(Y/p)`, the count of `k` for which the Legendre
indicator `1[n mod p < k mod p]` fires - i.e. for which `p ∣ C(n,k)`.

This is sharper than the paper's `(⌊Y/p⌋ - 1)(aₚ - 1)`: mathlib's exact residue
count (`Nat.count_modEq_card`) lets us keep the full `⌊Y/p⌋` per class.
-/
import Mathlib

open Finset

namespace BinomialThresholds

/-- Exactly-one-residue count, `≥` form: at least `Y / p` of the `k < Y` lie in a
fixed residue class `v < p`. (`Nat.count_modEq_card` gives `Y/p + [v < Y%p]`.) -/
theorem div_le_card_filter_mod_eq {p v Y : ℕ} (hp : 0 < p) (hv : v < p) :
    Y / p ≤ #{k ∈ Finset.range Y | k % p = v} := by
  have hset : {k ∈ Finset.range Y | k ≡ v [MOD p]} = {k ∈ Finset.range Y | k % p = v} :=
    Finset.filter_congr fun k _ => by rw [Nat.ModEq, Nat.mod_eq_of_lt hv]
  have hcount : #{k ∈ Finset.range Y | k % p = v} = Y / p + if v % p < Y % p then 1 else 0 := by
    have h := Nat.count_modEq_card Y hp v
    rw [Nat.count_eq_card_filter_range, hset] at h
    exact h
  omega

/-- **Block-counting bound.** For `t < p`, at least `(p - 1 - t)·(Y / p)` of the
`k < Y` satisfy `k mod p > t`. -/
theorem card_filter_mod_gt {p t Y : ℕ} (hp : 0 < p) (ht : t < p) :
    (p - 1 - t) * (Y / p) ≤ #{k ∈ Finset.range Y | t < k % p} := by
  -- decompose the `t < k % p` set into residue fibers `v ∈ (t, p)`.
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun k => k % p) (t := Finset.Ico (t + 1) p) (by
        intro k hk
        rw [Finset.coe_filter, Set.mem_setOf_eq] at hk
        exact Finset.mem_Ico.mpr ⟨hk.2, Nat.mod_lt k hp⟩)]
  -- each fiber equals the plain residue-class count (the `t < ·` is implied by `v > t`),
  -- which is `≥ Y / p`; there are `p - 1 - t` of them.
  have hfiber : ∀ v ∈ Finset.Ico (t + 1) p,
      Y / p ≤ #{k ∈ {k ∈ Finset.range Y | t < k % p} | k % p = v} := by
    intro v hv
    rw [Finset.mem_Ico] at hv
    rw [Finset.filter_filter]
    have hset : {k ∈ Finset.range Y | t < k % p ∧ k % p = v}
        = {k ∈ Finset.range Y | k % p = v} :=
      Finset.filter_congr fun k _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    rw [hset]
    exact div_le_card_filter_mod_eq hp hv.2
  calc (p - 1 - t) * (Y / p)
      = (Finset.Ico (t + 1) p).card * (Y / p) := by rw [Nat.card_Ico]; congr 1; omega
    _ = (Finset.Ico (t + 1) p).card • (Y / p) := by rw [smul_eq_mul]
    _ ≤ ∑ v ∈ Finset.Ico (t + 1) p, #{k ∈ {k ∈ Finset.range Y | t < k % p} | k % p = v} :=
        Finset.card_nsmul_le_sum _ _ _ hfiber

end BinomialThresholds
