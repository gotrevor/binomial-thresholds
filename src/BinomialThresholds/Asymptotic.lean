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
import BinomialThresholds.Upper

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

/-- The polynomial heart of the threshold (after clearing denominators by `4L²` and
substituting `Y ∈ [200L²−1, 200L²]`, `M ≈ Y/(2L)`, `H ≈ Y/2`). For `L ≥ 1000`,
`8YL³ < 0.6·L·(Y−2L)(Y−1) − (L+1)Y²/2 − 2.8L²Y`. Pure real-arithmetic, no floors. -/
theorem poly_heart {L Y : ℝ} (hL : 1000 ≤ L) (hYlo : 200 * L ^ 2 - 1 ≤ Y)
    (hYhi : Y ≤ 200 * L ^ 2) :
    8 * Y * L ^ 3 < 0.6 * L * (Y - 2 * L) * (Y - 1) - (L + 1) * Y ^ 2 / 2 - 2.8 * L ^ 2 * Y := by
  have hL0 : (0 : ℝ) < L := by linarith
  nlinarith [hL, hYlo, hYhi, hL0, sq_nonneg L, mul_pos hL0 hL0,
    mul_nonneg (mul_nonneg hL0.le hL0.le) hL0.le,
    mul_le_mul hYhi hYhi (by nlinarith [hYlo, hL0]) (by positivity),
    mul_nonneg hL0.le (by nlinarith [hYlo, hL0] : (0:ℝ) ≤ Y),
    mul_pos (mul_pos hL0 hL0) hL0]

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

set_option maxHeartbeats 3000000 in
/-- **Upper bound, witness form (constant-relaxed Theorem 2.1).** For large `n` there is an
explicit `k ≤ 200(log n)²` with `n² < u n k`. Assembles steps 3a–3d: with `Y = ⌊200(log n)²⌋`,
the single `j=2` term of `sum_lower_le_aux` (cutoff `M = ⌊Y/(2 log n)⌋`) exceeds `2·Y·log n`
(via the `θ ≥ 0.6x` Chebyshev lower bound and `poly_heart`), so `Upper.exists_threshold_le`
produces a `k ≤ Y ≤ 200(log n)²` in the threshold set. Both `f_le_polylog` (the `O((log n)²)`
bound) and `threshold_nonempty` (needed by the lower bound) are corollaries. -/
theorem eventually_exists_threshold :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ k : ℕ, (k : ℝ) ≤ 200 * (Real.log n) ^ 2 ∧ n ^ 2 < u n k := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp eventually_theta_ge
  have hlogtend : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogtend.eventually_ge_atTop (max x₀ 1000 + 1000),
    tendsto_natCast_atTop_atTop.eventually eventually_poly_log_le,
    tendsto_natCast_atTop_atTop.eventually eventually_log_le] with n hLbig hpoly hlogsmall
  set L : ℝ := Real.log (n : ℝ) with hLdef
  set Y : ℕ := ⌊200 * L ^ 2⌋₊ with hYdef
  set M : ℕ := ⌊(Y : ℝ) / (2 * L)⌋₊ with hMdef
  set H : ℕ := Y / 2 with hHdef
  clear_value Y M
  -- basic bounds on L, n
  have hL1000 : (1000 : ℝ) ≤ L := by have := le_max_right x₀ 1000; linarith
  have hLx0 : x₀ ≤ L := by have := le_max_left x₀ 1000; linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have h2L0 : (0 : ℝ) < 2 * L := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by positivity) hpoly
  have hn : 0 < n := by exact_mod_cast hnpos
  -- floor bounds on Y
  have hYhi : (Y : ℝ) ≤ 200 * L ^ 2 := by rw [hYdef]; exact Nat.floor_le (by positivity)
  have hYlo : 200 * L ^ 2 - 1 ≤ (Y : ℝ) := by
    rw [hYdef]; have := Nat.lt_floor_add_one (200 * L ^ 2); linarith
  have hYn : Y ≤ n := by have : (Y : ℝ) ≤ (n : ℝ) := le_trans hYhi hpoly; exact_mod_cast this
  -- bounds on H = Y/2
  have hH2 : 2 * (H : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (show 2 * H ≤ Y by omega)
  have hHlo : (Y : ℝ) - 1 ≤ 2 * (H : ℝ) := by
    have : (Y : ℝ) ≤ 2 * (H : ℝ) + 1 := by exact_mod_cast (show Y ≤ 2 * H + 1 by omega)
    linarith
  -- floor bounds on M, cleared of denominators
  have hMhi : (M : ℝ) ≤ (Y : ℝ) / (2 * L) := by rw [hMdef]; exact Nat.floor_le (by positivity)
  have hMlo : (Y : ℝ) / (2 * L) - 1 ≤ (M : ℝ) := by
    rw [hMdef]; have := Nat.lt_floor_add_one ((Y : ℝ) / (2 * L)); linarith
  have hMhi' : 2 * L * (M : ℝ) ≤ (Y : ℝ) := by
    have h : (M : ℝ) * (2 * L) ≤ Y := (le_div_iff₀ h2L0).mp hMhi; nlinarith [h]
  have hMlo' : (Y : ℝ) - 2 * L ≤ 2 * L * (M : ℝ) := by
    have h : (Y : ℝ) / (2 * L) ≤ (M : ℝ) + 1 := by linarith
    rw [div_le_iff₀ h2L0] at h; nlinarith [h]
  -- M ≤ n  (so log(n+M) ≤ log n + 1)
  have hM100L : (M : ℝ) ≤ 100 * L := by
    have h : 2 * L * (M : ℝ) ≤ 2 * L * (100 * L) := by nlinarith [le_trans hMhi' hYhi]
    exact le_of_mul_le_mul_left h h2L0
  have hMn : (M : ℝ) ≤ (n : ℝ) := by
    have h100n : 100 * L ≤ (n : ℝ) := by linarith
    linarith
  have hlog_nM : Real.log ((n : ℝ) + (M : ℝ)) ≤ L + 1 := by
    calc Real.log ((n : ℝ) + M) ≤ Real.log (2 * n) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Real.log n := Real.log_mul (by norm_num) (ne_of_gt hnpos)
      _ ≤ L + 1 := by have := Real.log_two_lt_d9; rw [← hLdef]; linarith
  -- θ(H) bounds
  have hHx0 : x₀ ≤ (H : ℝ) := by
    have hH_lo : 100 * L ^ 2 - 1 ≤ (H : ℝ) := by nlinarith [hHlo, hYlo]
    nlinarith [hH_lo, hLx0, hL1000]
  have hθlo : 0.6 * (H : ℝ) ≤ Chebyshev.theta (H : ℝ) := hx₀ (H : ℝ) hHx0
  have hθhi : Chebyshev.theta (H : ℝ) ≤ 1.4 * (H : ℝ) := by
    have h := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (H : ℝ) from Nat.cast_nonneg _)
    have hlog4 : Real.log 4 ≤ 1.4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; nlinarith
    nlinarith [h, mul_nonneg (by linarith : (0 : ℝ) ≤ 1.4 - Real.log 4) (Nat.cast_nonneg H : (0 : ℝ) ≤ (H : ℝ))]
  -- the cutoff sum and its product bounds
  set S : ℝ := ∑ A ∈ Finset.range M, (A : ℝ) with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg i)
  have hShi : S ≤ (M : ℝ) ^ 2 / 2 := sum_range_le_half_sq M
  clear_value S
  -- assemble: 2·Y·L  <  M·θ(H) − log(n+M)·S − θ(H)
  set θH : ℝ := Chebyshev.theta (H : ℝ) with hθdef
  clear_value θH
  have hAA : 0.6 * (M : ℝ) * (H : ℝ) ≤ (M : ℝ) * θH := by
    nlinarith [mul_le_mul_of_nonneg_left hθlo (Nat.cast_nonneg M : (0 : ℝ) ≤ (M : ℝ))]
  have hBB : Real.log ((n : ℝ) + M) * S ≤ (L + 1) * (M : ℝ) ^ 2 / 2 := by
    have hlogpos : 0 ≤ Real.log ((n : ℝ) + M) :=
      Real.log_nonneg (by linarith)
    calc Real.log ((n : ℝ) + M) * S ≤ (L + 1) * S := by nlinarith [hlog_nM, hS0]
      _ ≤ (L + 1) * ((M : ℝ) ^ 2 / 2) := by nlinarith [hShi, (show (0 : ℝ) ≤ L + 1 by linarith)]
      _ = (L + 1) * (M : ℝ) ^ 2 / 2 := by ring
  -- polynomial core (cleared by 4L²)
  have hY2L0 : (0 : ℝ) ≤ (Y : ℝ) - 2 * L := by nlinarith [hYlo, hL1000]
  have hY10 : (0 : ℝ) ≤ (Y : ℝ) - 1 := by nlinarith [hYlo, hL1000]
  have hLMH : ((Y : ℝ) - 2 * L) * ((Y : ℝ) - 1) ≤ 4 * L * (M : ℝ) * (H : ℝ) := by
    have h := mul_le_mul hMlo' hHlo hY10 (by positivity)
    nlinarith [h]
  have hM2sq : 4 * L ^ 2 * (M : ℝ) ^ 2 ≤ (Y : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 * L * (M : ℝ)) hMhi']
  have htarget : 2 * (Y : ℝ) * L < 0.6 * (M : ℝ) * (H : ℝ) - (L + 1) * (M : ℝ) ^ 2 / 2 - 1.4 * (H : ℝ) := by
    have hclear : 4 * L ^ 2 * (2 * (Y : ℝ) * L)
        < 4 * L ^ 2 * (0.6 * (M : ℝ) * (H : ℝ) - (L + 1) * (M : ℝ) ^ 2 / 2 - 1.4 * (H : ℝ)) := by
      have e1 : 0.6 * L * ((Y : ℝ) - 2 * L) * ((Y : ℝ) - 1) ≤ 2.4 * L ^ 2 * (M : ℝ) * (H : ℝ) := by
        nlinarith [hLMH, hL0]
      have e2 : 2 * L ^ 2 * (L + 1) * (M : ℝ) ^ 2 ≤ (L + 1) * (Y : ℝ) ^ 2 / 2 := by
        nlinarith [hM2sq, hL0]
      have e3 : 5.6 * L ^ 2 * (H : ℝ) ≤ 2.8 * L ^ 2 * (Y : ℝ) := by nlinarith [hH2, sq_nonneg L]
      nlinarith [poly_heart hL1000 hYlo hYhi, e1, e2, e3]
    exact lt_of_mul_lt_mul_left hclear (by positivity)
  -- chain through the aggregation and f_le_of_aux_sum_gt
  have hbig : 2 * (Y : ℝ) * L < ∑ p ∈ Nat.primesBelow (Y + 1),
      ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p := by
    have hfinal : 2 * (Y : ℝ) * L < (M : ℝ) * θH - Real.log ((n : ℝ) + M) * S - θH := by
      linarith [htarget, hAA, hBB, hθhi]
    rw [hθdef, hSdef] at hfinal
    have hagg := sum_lower_le_aux (n := n) (Y := Y) (J := 2) (fun _ => M) hn
    simp only [Finset.Icc_self, Finset.sum_singleton] at hagg
    rw [← hHdef] at hagg
    exact lt_of_lt_of_le hfinal hagg
  obtain ⟨k, hkY, hkey⟩ := exists_threshold_le hYn (by rw [← hLdef]; exact hbig)
  exact ⟨k, le_trans (by exact_mod_cast hkY) hYhi, hkey⟩

/-- **Upper bound (constant-relaxed Theorem 2.1): `f n = O((log n)²)`.** Concretely
`∃ C > 0, ∀ᶠ n, f n ≤ C·(log n)²` with `C = 200`. The witness `k` of
`eventually_exists_threshold` lies in the threshold set, so `f n = sInf … ≤ k ≤ 200(log n)²`. -/
theorem f_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, (f n : ℝ) ≤ C * (Real.log n) ^ 2 :=
  ⟨200, by norm_num, eventually_exists_threshold.mono fun n h => by
    obtain ⟨k, hk1, hk2⟩ := h
    have hfk : f n ≤ k := Nat.sInf_le hk2
    exact le_trans (by exact_mod_cast hfk) hk1⟩

/-- **The threshold set is eventually nonempty.** Corollary of `eventually_exists_threshold`:
for large `n` some `k` satisfies `n² < u n k`, so `{k | n² < u n k} ≠ ∅` and `f n` is a genuine
minimum (not the `sInf ∅ = 0` default). The lower bound `f_ge_log_frequently` needs this to
turn "no `k ≤ K` is in the set" into `K < f n`. -/
theorem threshold_nonempty :
    ∀ᶠ n : ℕ in Filter.atTop, {k | n ^ 2 < u n k}.Nonempty :=
  eventually_exists_threshold.mono fun n h => by
    obtain ⟨k, _, hk2⟩ := h
    exact ⟨k, hk2⟩

end BinomialThresholds
