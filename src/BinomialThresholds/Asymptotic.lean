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
open scoped Topology

namespace BinomialThresholds

/-- **Sqrt smallness (3d error control).** `2√x·log x ≤ x/100` eventually. The `√x·log x`
correction in `theta_ge` is `o(x)`; this packages exactly the bound needed to absorb it.
From `isLittleO_log_rpow_atTop` (`log =o x^{1/2}`) with `c = 1/200`. -/
theorem eventually_two_sqrt_log_le :
    ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.sqrt x * Real.log x ≤ x / 100 := by
  have hlit : Real.log =o[Filter.atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hb := Asymptotics.isLittleO_iff.mp hlit (show (0 : ℝ) < 1 / 200 by norm_num)
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg hx0 _), ← Real.sqrt_eq_rpow] at hx
  nlinarith [hx, Real.sqrt_nonneg x, Real.mul_self_sqrt hx0]

/-- **Log smallness (3d error control).** `log x ≤ x/100` eventually, from
`Real.isLittleO_log_id_atTop`. -/
theorem eventually_log_le :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x / 100 := by
  have hb := Asymptotics.isLittleO_iff.mp Real.isLittleO_log_id_atTop
    (show (0 : ℝ) < 1 / 100 by norm_num)
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (by simp only [id_eq]; linarith : (0 : ℝ) ≤ id x)] at hx
  simp only [id_eq] at hx; linarith

/-- **Linear Chebyshev lower bound (3d).** `θ(x) ≥ 0.6·x` eventually. Combines the `theta_ge`
engine (`θ(x) ≥ x·log2 − 2log2 − log x − 2√x·log x`) with the smallness bounds, using
`log 2 > 0.6931` (`Real.log_two_gt_d9`) to clear the gap `log2 − 0.6 ≈ 0.093`. The relaxed
coefficient `0.6 < log 2` buys the room to absorb the `o(x)` corrections. -/
theorem eventually_theta_ge :
    ∀ᶠ x : ℝ in Filter.atTop, 0.6 * x ≤ Chebyshev.theta x := by
  filter_upwards [eventually_two_sqrt_log_le, eventually_log_le,
    Filter.eventually_ge_atTop (2 : ℝ), Filter.eventually_ge_atTop (200 : ℝ)]
    with x hsq hlg hx2 hx200
  have ht := theta_ge hx2
  nlinarith [ht, hsq, hlg, hx200, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Gauss-sum bound: `∑_{A<M} A ≤ M²/2`. -/
theorem sum_range_le_half_sq (M : ℕ) :
    ∑ A ∈ Finset.range M, (A : ℝ) ≤ (M : ℝ) ^ 2 / 2 := by
  have h : (∑ i ∈ Finset.range M, i) * 2 = M * (M - 1) := Finset.sum_range_id_mul_two M
  have h2 : (∑ A ∈ Finset.range M, (A : ℝ)) * 2 = ((M * (M - 1) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast h
  have h3 : ((M * (M - 1) : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
    calc ((M * (M - 1) : ℕ) : ℝ) ≤ ((M * M : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul (le_refl M) (Nat.sub_le M 1)
      _ = (M : ℝ) ^ 2 := by push_cast; ring
  linarith

/-- `(log x)² = o(x)`: concretely `200·(log x)² ≤ x` eventually. Needed for `Y ≤ n` and
`Mⱼ ≤ n` (so `log(n+Mⱼ) ≤ log n + 1`). From `log =o x^{1/2}` with `c = 1/15`. -/
theorem eventually_poly_log_le :
    ∀ᶠ x : ℝ in Filter.atTop, 200 * (Real.log x) ^ 2 ≤ x := by
  have hlit : Real.log =o[Filter.atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hb := Asymptotics.isLittleO_iff.mp hlit (show (0 : ℝ) < 1 / 15 by norm_num)
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg hx0 _), ← Real.sqrt_eq_rpow] at hx
  nlinarith [hx, Real.log_nonneg hx1, Real.sqrt_nonneg x, Real.mul_self_sqrt hx0]

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
