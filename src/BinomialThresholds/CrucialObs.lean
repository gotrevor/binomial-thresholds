/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

The "crucial observation" of arXiv:2603.29961 §2 (upper bound). For a prime `p`,
write `aₚ = p - (n mod p)` (the distance from `n` up to the next multiple of `p`).
If `aₚ ≤ A` then `p` divides one of `n+1, …, n+A`. Consequently a *set* of distinct
primes each with `aₚ ≤ A` has product dividing `∏_{m=1}^A (n+m)`, which bounds
`∑_{aₚ ≤ A} log p ≤ log ∏(n+m)`. This is what rules out `n mod p` being close to `p`
for too many `p` at once.
-/
import Mathlib

open Finset

namespace BinomialThresholds

/-- `p` divides `n + (p - n mod p)`: stepping up from `n` by `aₚ = p - n mod p` lands
on the next multiple of `p`. -/
theorem dvd_add_sub_mod {p : ℕ} (hp : 0 < p) (n : ℕ) : p ∣ n + (p - n % p) := by
  obtain ⟨q, hq⟩ : ∃ q, n = p * q + n % p := ⟨n / p, (Nat.div_add_mod n p).symm⟩
  have hr : n % p < p := Nat.mod_lt n hp
  refine ⟨q + 1, ?_⟩
  rw [Nat.mul_succ]
  omega

/-- **The crucial observation.** Distinct primes `p` with `aₚ = p - n mod p ≤ A` have
product dividing `∏_{m ∈ [1,A]} (n + m)` — each such `p` divides the shift `n + aₚ`,
and distinct primes are pairwise coprime. -/
theorem prod_primes_dvd_prod_shift {n A : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hA : ∀ p ∈ S, p - n % p ≤ A) :
    (∏ p ∈ S, p) ∣ ∏ m ∈ Finset.Icc 1 A, (n + m) := by
  apply Finset.prod_primes_dvd
  · exact fun p hp => (hS p hp).prime
  · intro p hp
    have hppos := (hS p hp).pos
    have hr : n % p < p := Nat.mod_lt n hppos
    -- `aₚ = p - n % p ∈ [1, A]`, and `p ∣ n + aₚ`, a factor of the product.
    have hmem : p - n % p ∈ Finset.Icc 1 A :=
      Finset.mem_Icc.mpr ⟨by omega, hA p hp⟩
    exact (dvd_add_sub_mod hppos n).trans (Finset.dvd_prod_of_mem (fun m => n + m) hmem)

/-- **Crucial observation, log form.** Taking logs of `prod_primes_dvd_prod_shift`:
distinct primes with `aₚ ≤ A` satisfy `∑ log p ≤ A · log(n + A)`. This is the
inequality the upper-bound averaging consumes (with `log(n+A)` later bounded by
`log n + log Mⱼ`). -/
theorem sum_log_le_of_a_le {n A : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hA : ∀ p ∈ S, p - n % p ≤ A) :
    ∑ p ∈ S, Real.log p ≤ A * Real.log (n + A) := by
  have hSpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  have hprodpos : 0 < ∏ m ∈ Finset.Icc 1 A, (n + m) :=
    Finset.prod_pos fun m hm => by have := (Finset.mem_Icc.mp hm).1; omega
  have hle : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ ((∏ m ∈ Finset.Icc 1 A, (n + m) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hprodpos (prod_primes_dvd_prod_shift hS hA)
  have e1 : ∑ p ∈ S, Real.log (p : ℝ) = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod fun p hp => by exact_mod_cast (hS p hp).pos.ne']
  calc ∑ p ∈ S, Real.log (p : ℝ)
      = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := e1
    _ ≤ Real.log ((∏ m ∈ Finset.Icc 1 A, (n + m) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hSpos) hle
    _ = ∑ m ∈ Finset.Icc 1 A, Real.log ((n + m : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod fun m hm => by
          have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (by omega : (0 : ℕ) < n + m).ne']
    _ ≤ ∑ m ∈ Finset.Icc 1 A, Real.log ((n : ℝ) + A) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have h1 := (Finset.mem_Icc.mp hm).1
        have h2 := (Finset.mem_Icc.mp hm).2
        refine Real.log_le_log (by exact_mod_cast (by omega : (0 : ℕ) < n + m)) ?_
        push_cast; exact_mod_cast by omega
    _ = A * Real.log ((n : ℝ) + A) := by
        rw [Finset.sum_const, Nat.card_Icc]; push_cast; ring

end BinomialThresholds
