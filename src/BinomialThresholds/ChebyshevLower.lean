/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

Step 3c of the upper bound (arXiv:2603.29961 §2): a **Chebyshev lower bound** on
`θ`/`ψ`. mathlib v4.29.1 ships only the *upper* Chebyshev bounds, so we build the lower
bound from the central binomial coefficient:

  `4ⁿ ≤ 2n·C(2n,n)`  (`four_pow_le_two_mul_self_mul_centralBinom`)
  ⟹ `2n·log2 - log(2n) ≤ log C(2n,n) ≤ ψ(2n)`  ⟹  `θ(2n) ≥ ψ(2n) - 2√(2n)·log(2n)`.

The crux is `log C(2n,n) ≤ ψ(2n)`: via the von Mangoldt divisor identity
`∑_{d ∣ N} Λ d = log N`, only prime-power divisors contribute, and every prime-power
divisor of `C(2n,n)` is `≤ 2n` (its prime appears to power `≤ v_p ≤ log_p(2n)`).
-/
import Mathlib

open Finset
open scoped ArithmeticFunction

namespace BinomialThresholds

/-- **The von Mangoldt half (step 3c core).** `log C(2n,n) ≤ ψ(2n)`: the divisor identity
`log N = ∑_{d ∣ N} Λ d` keeps only prime-power divisors, each of which is `≤ 2n` (a prime
power `pᵏ ∣ C(2n,n)` has `k ≤ v_p(C(2n,n))`, so `pᵏ ≤ p^{v_p} ≤ 2n`). Those land in
`Ioc 0 (2n)`, and `ψ(2n) = ∑_{m ≤ 2n} Λ m` with `Λ ≥ 0` dominates. -/
theorem log_centralBinom_le_psi {n : ℕ} (hn : 0 < n) :
    Real.log (Nat.centralBinom n) ≤ Chebyshev.psi (2 * n) := by
  -- (1) log N = ∑ over the prime-power divisors of Λ (non prime powers contribute 0).
  have hlog : Real.log (Nat.centralBinom n)
      = ∑ d ∈ (Nat.centralBinom n).divisors.filter (fun d => IsPrimePow d), Λ d := by
    rw [← ArithmeticFunction.vonMangoldt_sum (n := Nat.centralBinom n)]
    refine (Finset.sum_filter_of_ne (fun d _ hne => ?_)).symm
    by_contra hpp
    exact hne (by rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp])
  -- (2) every prime-power divisor of C(2n,n) lies in Ioc 0 (2n).
  have hsub : (Nat.centralBinom n).divisors.filter (fun d => IsPrimePow d)
      ⊆ Finset.Ioc 0 (2 * n) := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hpp⟩ := hd
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
    rw [Finset.mem_Ioc]
    refine ⟨pow_pos hp.pos k, ?_⟩
    -- k ≤ v_p(C(2n,n)), so pᵏ ≤ p^{v_p} ≤ 2n.
    have hkle : k ≤ (Nat.centralBinom n).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.centralBinom_pos n).ne').mp hdvd
    have hpow : p ^ ((Nat.centralBinom n).factorization p) ≤ 2 * n := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact Nat.pow_factorization_choose_le (by omega)
    exact le_trans (Nat.pow_le_pow_right hp.one_lt.le hkle) hpow
  -- (3) drop to a subsum of ψ(2n) = ∑_{m ∈ Ioc 0 (2n)} Λ m.
  have hfloor : ⌊(2 * n : ℝ)⌋₊ = 2 * n := by
    rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hlog, Chebyshev.psi, hfloor]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- **The central-binomial half (step 3c).** `2n·log2 - log(2n) ≤ ψ(2n)`: from
`4ⁿ ≤ 2n·C(2n,n)` (`four_pow_le_two_mul_self_mul_centralBinom`), take logs
(`log 4ⁿ = 2n·log2`, `log(2n·C) = log(2n) + log C`) and chain through
`log C ≤ ψ(2n)`. -/
theorem two_mul_log_two_le_psi {n : ℕ} (hn : 0 < n) :
    2 * n * Real.log 2 - Real.log (2 * n) ≤ Chebyshev.psi (2 * n) := by
  have hB : ((4 : ℝ)) ^ n ≤ 2 * n * Nat.centralBinom n := by
    exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hCpos : (0 : ℝ) < Nat.centralBinom n := by exact_mod_cast Nat.centralBinom_pos n
  have h2n : (0 : ℝ) < 2 * n := by exact_mod_cast (by omega : 0 < 2 * n)
  have hlog4 : Real.log ((4 : ℝ) ^ n) = 2 * n * Real.log 2 := by
    rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hmono : Real.log ((4 : ℝ) ^ n) ≤ Real.log (2 * n * Nat.centralBinom n) :=
    Real.log_le_log (by positivity) hB
  rw [hlog4, Real.log_mul h2n.ne' hCpos.ne'] at hmono
  linarith [log_centralBinom_le_psi hn]

/-- **Chebyshev θ lower bound at even integers (step 3c, assembled).**
`θ(2n) ≥ 2n·log2 - log(2n) - 2·√(2n)·log(2n)`. Combines the ψ lower bound with the
elementary ψ≈θ gap `|ψ - θ| ≤ 2√x·log x` (`abs_psi_sub_theta_le_sqrt_mul_log`). The
`√x·log x` correction is `o(x)`, so the main term is the relaxed Chebyshev constant
`log 2 ≈ 0.693` that the upper-bound averaging (step 3d) needs. -/
theorem theta_lower {n : ℕ} (hn : 0 < n) :
    2 * n * Real.log 2 - Real.log (2 * n) - 2 * Real.sqrt (2 * n) * Real.log (2 * n)
      ≤ Chebyshev.theta (2 * n) := by
  have hx : (1 : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : 1 ≤ 2 * n)
  have hgap : Chebyshev.psi (2 * n) - Chebyshev.theta (2 * n)
      ≤ 2 * Real.sqrt (2 * n) * Real.log (2 * n) :=
    le_trans (le_abs_self _) (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx)
  linarith [two_mul_log_two_le_psi hn]

end BinomialThresholds
