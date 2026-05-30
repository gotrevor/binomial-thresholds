/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

The Legendre / Kummer building block for the binomial-threshold proof:

  `v_p( C(n,k) ) ≥ 1[ n mod p < k mod p ]`.

This is the atomic inequality the paper uses in both the upper and lower bounds
(arXiv:2603.29961 §2). The upper bound sums it over `k`; the lower bound uses its
contrapositive (a carry-free residue pattern forces `v_p = 0`).
-/
import Mathlib

open Finset

namespace BinomialThresholds

/-- **Carry characterization.** Adding `k` and `n - k` in base-`m` carries out of a
digit position (`m ≤ k % m + (n - k) % m`) exactly when that digit of `n` is smaller
than that of `k` (`n % m < k % m`). Here `m` is the place value `p^i`; `k ≤ n`. -/
theorem m_le_mod_add_mod_iff {m n k : ℕ} (hm : 0 < m) (hkn : k ≤ n) :
    m ≤ k % m + (n - k) % m ↔ n % m < k % m := by
  set s := k % m + (n - k) % m with hs
  have hka : k % m < m := Nat.mod_lt _ hm
  have hnka : (n - k) % m < m := Nat.mod_lt _ hm
  have hsum : n % m = s % m := by
    conv_lhs => rw [← Nat.add_sub_cancel' hkn, Nat.add_mod]
  rcases lt_or_ge s m with hsm | hsm
  · -- no carry: `s % m = s`, so both sides are false.
    rw [Nat.mod_eq_of_lt hsm] at hsum
    simp only [hsum]; omega
  · -- carry: `s % m = s - m`, so both sides are true.
    have : s % m = s - m := by
      conv_lhs => rw [show s = (s - m) + m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [this] at hsum
    simp only [hsum]; omega

/-- **Carry ⇒ divisibility (single digit).** Convenience direction of
`m_le_mod_add_mod_iff` at the units place `m = p`. -/
theorem p_le_mod_add_mod_of_mod_lt {p n k : ℕ} (hp : 0 < p) (hkn : k ≤ n)
    (hlt : n % p < k % p) : p ≤ k % p + (n - k) % p :=
  (m_le_mod_add_mod_iff hp hkn).mpr hlt

/-- **Legendre lower bound.** For a prime `p` and `k ≤ n`, if `n % p < k % p` then
`p` divides `C(n,k)`, i.e. `1 ≤ v_p( C(n,k) )`. -/
theorem one_le_factorization_choose {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hlt : n % p < k % p) : 1 ≤ (n.choose k).factorization p := by
  -- `n % p < k % p ≤ k ≤ n` with `k % p < p` forces `p ≤ n` (else `n % p = n ≥ k = k % p`).
  have hpn : p ≤ n := by
    by_contra hc
    push Not at hc
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (lt_of_le_of_lt hkn hc)] at hlt
    omega
  -- so `1 ≤ log p n`, giving a nonempty index window `Ico 1 (log p n + 1)`.
  have hlog : 0 < Nat.log p n :=
    Nat.le_log_of_pow_le hp.one_lt (by simpa using hpn)
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  apply Finset.card_pos.mpr
  refine ⟨1, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨le_rfl, by omega⟩, ?_⟩
  simpa [pow_one] using p_le_mod_add_mod_of_mod_lt hp.pos hkn hlt

/-- **Legendre zero (no-carry).** For a prime `p` and `k ≤ n`, if at every place
value `p^i` the digit of `n` is at least that of `k` (`k % p^i ≤ n % p^i`), then `p`
does not divide `C(n,k)`: `v_p( C(n,k) ) = 0`. This is the carry-free pattern the
lower bound's witness family is engineered to produce. -/
theorem factorization_choose_eq_zero {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (h : ∀ i, k % p ^ i ≤ n % p ^ i) : (n.choose k).factorization p = 0 := by
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  -- the carry predicate fails at every `i`: no carry since `n`'s digit ≥ `k`'s digit.
  rw [not_le]
  exact (not_le.mp ((m_le_mod_add_mod_iff (pow_pos hp.pos i) hkn).not.mpr
    (not_lt.mpr (h i))))

end BinomialThresholds
