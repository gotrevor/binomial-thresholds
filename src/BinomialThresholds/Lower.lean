/-
Copyright (c) 2026. Trevor Morris.
Released under Apache 2.0 license.

The **lower bound** (constant-relaxed): `f n ≥ c · log n` infinitely often
(arXiv:2603.29961 §2). Witness family `n = M_K − 1` where

  `M_K = ∏_{p ≤ K, p prime} p ^ (⌊log_p K⌋ + 1)`.

For every `k ≤ K` and prime `p ≤ K`, the prime power `p^{⌊log_p K⌋+1}` divides `M_K`
and exceeds `K ≥ k`, so the base-`p` digits of `n = M_K − 1` dominate those of `k` at
every place value (`k % pⁱ ≤ n % pⁱ`). By `Legendre.factorization_choose_eq_zero` this
is a *carry-free* pattern, forcing `vₚ(C(n,k)) = 0`. Hence `u(n,k) = 1` for all `k ≤ K`,
so no `k ≤ K` lies in the threshold set `{k | n² < u n k}` and therefore `K < f n`.

Finally `log n ≤ log M_K = ψ(K) + θ(K) = O(K)` (the `O(K)`, not `O(K log K)`, needs the
Chebyshev structure: `log(∏ p^{⌊log_p K⌋}) ≤ ψ(K) ≤ (log 4 + 4)·K`), giving
`c · log n ≤ K < f n` with `c = 1/(2 log 4 + 4)`. The `∃ᶠ` comes from `M_K − 1 → ∞`.
-/
import Mathlib
import BinomialThresholds.Basic
import BinomialThresholds.Legendre
import BinomialThresholds.Asymptotic

open Filter Finset
open scoped BigOperators Topology ArithmeticFunction

namespace BinomialThresholds

/-- `(M − 1) % d = d − 1` when `d ∣ M` and `M > 0`: the predecessor of a positive multiple
of `d` has maximal residue. -/
theorem pred_mod_of_dvd {d M : ℕ} (hd : d ∣ M) (hMpos : 0 < M) : (M - 1) % d = d - 1 := by
  obtain ⟨t, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hMpos)
  have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at hMpos)
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have he : d * (s + 1) = d * s + d := by ring
  have hcomm : d * s = s * d := Nat.mul_comm d s
  have h3 : d * (s + 1) - 1 = (d - 1) + s * d := by rw [he]; omega
  rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- The witness numerator `M_K = ∏_{p ≤ K, prime} p^(⌊log_p K⌋ + 1)`. -/
noncomputable def MK (K : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesBelow (K + 1), p ^ (Nat.log p K + 1)

theorem MK_pos (K : ℕ) : 0 < MK K :=
  Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primesBelow hp).pos _

/-- For prime `p ≤ K`, the maximal prime power `p^(⌊log_p K⌋+1)` divides `M_K`. -/
theorem pow_dvd_MK {p K : ℕ} (hp : p.Prime) (hpK : p ≤ K) :
    p ^ (Nat.log p K + 1) ∣ MK K :=
  Finset.dvd_prod_of_mem (fun q => q ^ (Nat.log q K + 1))
    (Nat.mem_primesBelow.mpr ⟨by omega, hp⟩)

/-- `K < M_K`: the `p = 2` factor already exceeds `K` (needs `2 ≤ K`). -/
theorem lt_MK {K : ℕ} (hK : 2 ≤ K) : K < MK K := by
  have h2 : (2 : ℕ).Prime := Nat.prime_two
  have hdvd : 2 ^ (Nat.log 2 K + 1) ∣ MK K := pow_dvd_MK h2 hK
  have hle : 2 ^ (Nat.log 2 K + 1) ≤ MK K := Nat.le_of_dvd (MK_pos K) hdvd
  exact lt_of_lt_of_le (Nat.lt_pow_succ_log_self h2.one_lt K) hle

/-- **Digit domination.** For prime `p ≤ K`, `k ≤ K`, and every place value `pⁱ`, the
`i`-th base-`p` digit of `M_K − 1` is at least that of `k`: `k % pⁱ ≤ (M_K − 1) % pⁱ`.
Split at `a = ⌊log_p K⌋+1`: for `i ≤ a`, `pⁱ ∣ M_K` so `(M_K−1) % pⁱ = pⁱ−1` is maximal;
for `i > a`, `k < pᵃ ≤ (M_K−1) % pⁱ` because `(M_K−1) % pⁱ ≡ M_K−1 ≡ pᵃ−1 (mod pᵃ)`. -/
theorem digit_le {p K : ℕ} (hp : p.Prime) (hpK : p ≤ K) {k : ℕ} (hk : k ≤ K) (i : ℕ) :
    k % p ^ i ≤ (MK K - 1) % p ^ i := by
  set a := Nat.log p K + 1 with ha
  have hMpos : 0 < MK K := MK_pos K
  have hpa_dvd : p ^ a ∣ MK K := pow_dvd_MK hp hpK
  have hKpa : K < p ^ a := Nat.lt_pow_succ_log_self hp.one_lt K
  rcases le_or_gt i a with hia | hia
  · -- `pⁱ ∣ pᵃ ∣ M_K`, so `(M_K−1) % pⁱ = pⁱ − 1` is the maximal possible residue.
    have hpi_dvd : p ^ i ∣ MK K := dvd_trans (pow_dvd_pow p hia) hpa_dvd
    rw [pred_mod_of_dvd hpi_dvd hMpos]
    exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (pow_pos hp.pos i))
  · -- `i > a`: `k < pᵃ ≤ pⁱ` gives `k % pⁱ = k`, and `pᵃ ∣ pⁱ` projects the residue.
    have hkpa : k < p ^ a := lt_of_le_of_lt hk hKpa
    have hpa_pi : p ^ a ∣ p ^ i := pow_dvd_pow p hia.le
    have hmod_k : k % p ^ i = k :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hkpa (Nat.pow_le_pow_right hp.pos hia.le))
    rw [hmod_k]
    -- `((M_K−1) % pⁱ) % pᵃ = (M_K−1) % pᵃ = pᵃ − 1 ≥ k`.
    have hproj : (MK K - 1) % p ^ i % p ^ a = p ^ a - 1 := by
      rw [Nat.mod_mod_of_dvd _ hpa_pi, pred_mod_of_dvd hpa_dvd hMpos]
    calc k ≤ p ^ a - 1 := by omega
      _ = (MK K - 1) % p ^ i % p ^ a := hproj.symm
      _ ≤ (MK K - 1) % p ^ i := Nat.mod_le _ _

/-- **`u` collapses on the witness.** For `k ≤ K`, every prime `p ≤ k ≤ K` has a carry-free
digit pattern between `k` and `n = M_K − 1` (`digit_le`), so `vₚ(C(n,k)) = 0` by
`factorization_choose_eq_zero`; hence every factor of `u (M_K−1) k` is `p^0 = 1`. -/
theorem u_MK_eq_one {K : ℕ} (hK : 2 ≤ K) {k : ℕ} (hk : k ≤ K) :
    u (MK K - 1) k = 1 := by
  have hkn : k ≤ MK K - 1 := by have := lt_MK hK; omega
  unfold u
  refine Finset.prod_eq_one fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesBelow hp
  have hp_lt : p < k + 1 := (Nat.mem_primesBelow.mp hp).1
  have hpk : p ≤ k := by omega
  have hpK : p ≤ K := le_trans hpk hk
  have hzero : ((MK K - 1).choose k).factorization p = 0 :=
    factorization_choose_eq_zero hpp hkn (fun i => digit_le hpp hpK hk i)
  rw [hzero, pow_zero]

/-! ### The analytic bound `log M_K = O(K)` -/

/-- `∏_{p ≤ K, prime} p^(⌊log_p K⌋)` — the `lcm(1..K)` factor of `M_K` (one power lower than
`M_K` in each prime). Its log is `ψ(K)`, which Chebyshev bounds by `O(K)`. -/
noncomputable def LK (K : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesBelow (K + 1), p ^ (Nat.log p K)

theorem LK_pos (K : ℕ) : 0 < LK K :=
  Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primesBelow hp).pos _

/-- The `p`-adic valuation of `L_K` is `⌊log_p K⌋` for prime `p ≤ K`, else `0`. -/
theorem factorization_LK (K q : ℕ) :
    (LK K).factorization q = if q ∈ Nat.primesBelow (K + 1) then Nat.log q K else 0 := by
  unfold LK
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primesBelow hp).pos.ne')]
  rw [Finset.sum_apply']
  have hcongr : ∀ p ∈ Nat.primesBelow (K + 1),
      (p ^ Nat.log p K).factorization q = if p = q then Nat.log p K else 0 := by
    intro p hp
    rw [(Nat.prime_of_mem_primesBelow hp).factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']

/-- **`log L_K ≤ ψ(K)`** (the key `O(K)` cancellation). Every prime-power divisor `pʲ` of
`L_K` satisfies `j ≤ vₚ(L_K) = ⌊log_p K⌋`, so `pʲ ≤ p^{⌊log_p K⌋} ≤ K`; thus all prime-power
divisors lie in `Ioc 0 K` and `log L_K = ∑_{d ∣ L_K} Λ d = ∑_{d ∣ L_K, primepow} Λ d` is a
subsum of `ψ(K) = ∑_{m ≤ K} Λ m`. Mirrors `ChebyshevLower.log_centralBinom_le_psi`. -/
theorem log_LK_le_psi {K : ℕ} (hK : 1 ≤ K) :
    Real.log (LK K) ≤ Chebyshev.psi K := by
  have hLpos : 0 < LK K := LK_pos K
  have hlog : Real.log (LK K)
      = ∑ d ∈ (LK K).divisors.filter (fun d => IsPrimePow d), Λ d := by
    rw [← ArithmeticFunction.vonMangoldt_sum (n := LK K)]
    refine (Finset.sum_filter_of_ne (fun d _ hne => ?_)).symm
    by_contra hpp
    exact hne (by rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp])
  have hsub : (LK K).divisors.filter (fun d => IsPrimePow d) ⊆ Finset.Ioc 0 K := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hpp⟩ := hd
    obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
    rw [Finset.mem_Ioc]
    refine ⟨pow_pos hp.pos j, ?_⟩
    -- j ≤ v_p(L_K) = log_p K, so p^j ≤ p^{log_p K} ≤ K.
    have hjle : j ≤ (LK K).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hLpos.ne').mp hdvd
    have hpmem : p ∈ Nat.primesBelow (K + 1) := by
      by_contra hmem
      rw [factorization_LK, if_neg hmem] at hjle
      omega
    rw [factorization_LK, if_pos hpmem] at hjle
    calc p ^ j ≤ p ^ (Nat.log p K) := Nat.pow_le_pow_right hp.pos hjle
      _ ≤ K := Nat.pow_log_le_self p (by omega)
  have hfloor : ⌊(K : ℝ)⌋₊ = K := Nat.floor_natCast K
  rw [hlog, Chebyshev.psi, hfloor]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- `log M_K = log L_K + θ(K)` — peeling the extra `+1` power off each prime of `M_K`. -/
theorem log_MK_eq {K : ℕ} :
    Real.log (MK K) = Real.log (LK K) + Chebyshev.theta K := by
  have hprime : ∀ p ∈ Nat.primesBelow (K + 1), p.Prime := fun p hp =>
    Nat.prime_of_mem_primesBelow hp
  have hM : Real.log (MK K)
      = ∑ p ∈ Nat.primesBelow (K + 1), ((Nat.log p K : ℝ) + 1) * Real.log p := by
    unfold MK
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
    · intro p hp
      exact_mod_cast (pow_pos (hprime p hp).pos _).ne'
  have hL : Real.log (LK K)
      = ∑ p ∈ Nat.primesBelow (K + 1), (Nat.log p K : ℝ) * Real.log p := by
    unfold LK
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      exact_mod_cast (pow_pos (hprime p hp).pos _).ne'
  have hθ : Chebyshev.theta K = ∑ p ∈ Nat.primesBelow (K + 1), Real.log p := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    unfold primorial
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p; simp [Nat.mem_primesBelow]
    · intro p hp
      have : p.Prime := (Finset.mem_filter.mp hp).2
      exact_mod_cast this.pos.ne'
  rw [hM, hL, hθ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **`log M_K = O(K)`.** Concretely `log M_K ≤ (2 log 4 + 4)·K`: combine
`log L_K ≤ ψ(K) ≤ (log 4 + 4)·K` (Chebyshev) with `θ(K) ≤ (log 4)·K`. -/
theorem log_MK_le {K : ℕ} (hK : 1 ≤ K) :
    Real.log (MK K) ≤ (2 * Real.log 4 + 4) * K := by
  rw [log_MK_eq]
  have h1 : Real.log (LK K) ≤ Chebyshev.psi K := log_LK_le_psi hK
  have h2 : Chebyshev.psi K ≤ (Real.log 4 + 4) * K :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have h3 : Chebyshev.theta K ≤ Real.log 4 * K :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  nlinarith [h1, h2, h3]

/-! ### Assembly -/

/-- **Lower bound (constant-relaxed): `f n ≥ c · log n` infinitely often.** Paper gives
`(1/2 + o(1)) log nⱼ`; we relax to some `c > 0`. Witness `n = M_K − 1` with `K → ∞`:
`u(n,k) = 1` for `k ≤ K` (`u_MK_eq_one`) puts the whole interval `[0,K]` outside the
(eventually nonempty, by `threshold_nonempty`) threshold set, so `K < f n`; and
`log n ≤ log M_K ≤ C·K` (`log_MK_le`) gives `(1/C)·log n ≤ K < f n`. -/
theorem f_ge_log_frequently :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, c * Real.log n ≤ (f n : ℝ) := by
  set C : ℝ := 2 * Real.log 4 + 4 with hC
  have hCpos : 0 < C := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    rw [hC]; linarith
  refine ⟨1 / C, by positivity, ?_⟩
  -- threshold set eventually nonempty: get a threshold `N₀` beyond which it holds.
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp threshold_nonempty
  rw [Filter.frequently_atTop]
  intro N
  -- choose K large enough: K ≥ 2, and n = M_K − 1 ≥ max(N, N₀).
  set K := max 2 (max N N₀) with hKdef
  have hK2 : 2 ≤ K := le_max_left _ _
  have hKN : N ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKN₀ : N₀ ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  set n := MK K - 1 with hndef
  have hlt : K < MK K := lt_MK hK2
  have hnK : K ≤ n := by rw [hndef]; omega
  refine ⟨n, le_trans hKN hnK, ?_⟩
  -- nonempty threshold set for n (since n ≥ N₀).
  have hne : {k | n ^ 2 < u n k}.Nonempty := hN₀ n (le_trans hKN₀ hnK)
  -- no k ≤ K is in the threshold set.
  have hnotmem : ∀ k, k ≤ K → k ∉ {k | n ^ 2 < u n k} := by
    intro k hk hmem
    have hu1 : u n k = 1 := u_MK_eq_one hK2 hk
    have hlt1 : n ^ 2 < 1 := by rw [← hu1]; exact hmem
    have hnpos : 0 < n := by omega
    have : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n hnpos
    omega
  -- so f n = sInf S > K.
  have hfn : K < f n := by
    have hmem : f n ∈ {k | n ^ 2 < u n k} := Nat.sInf_mem hne
    by_contra hle
    push Not at hle
    exact hnotmem (f n) hle hmem
  -- combine with log n ≤ C·K and K ≤ f n.
  have hnpos : 0 < n := by omega
  have hlogn : Real.log n ≤ C * K := by
    have hmono : Real.log (n : ℝ) ≤ Real.log (MK K : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast hnpos)
      exact_mod_cast Nat.sub_le _ 1
    exact le_trans hmono (log_MK_le (by omega))
  have hKf : (K : ℝ) ≤ (f n : ℝ) := by exact_mod_cast hfn.le
  calc (1 / C) * Real.log n ≤ (1 / C) * (C * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogn (by positivity)
    _ = (K : ℝ) := by rw [one_div, ← mul_assoc, inv_mul_cancel₀ hCpos.ne', one_mul]
    _ ≤ (f n : ℝ) := hKf

end BinomialThresholds
