# Binomial Thresholds — master handoff

**Status (2026-05-30)**: §2 of arXiv:2603.29961 — **COMPLETE. Both bounds proven &
axiom-clean. Zero sorries.**

## What this is

Constant-relaxed formalization of Erdős #684 (small prime factors of `C(n,k)`):
- `f_le_polylog : ∃ C>0, ∀ᶠ n, f n ≤ C·(log n)²` — **PROVEN, axiom-clean.** (`C = 200`)
- `f_ge_log_frequently : ∃ c>0, ∃ᶠ n, c·log n ≤ f n` — **PROVEN, axiom-clean.**
  (`c = 1/(2 log 4 + 4)`)

`#print axioms` for both → `[propext, Classical.choice, Quot.sound]` (the three standard
mathlib axioms; nothing custom). Full build green: `lake build BinomialThresholds` → 8259 jobs.

## Module map

| File | Role | State |
|------|------|-------|
| `Basic.lean` | `u`, `f` defs | ✅ |
| `Legendre.lean` | `v_p(C(n,k))` carry lemmas (both directions) | ✅ |
| `CrucialObs.lean` | step-1 crucial observation | ✅ |
| `BlockCount.lean` | step-2 block counting | ✅ |
| `Aggregation.lean` | step-2 aggregation | ✅ |
| `Decomposition.lean` | step-3a j-decomposition | ✅ |
| `ChebyshevLower.lean` | θ/ψ lower bound (built, mathlib lacks it) | ✅ |
| `Asymptotic.lean` | step-3d assembly → `eventually_exists_threshold`, `f_le_polylog`, `threshold_nonempty` | ✅ |
| `Upper.lean` | averaging → `exists_threshold_le`, `f_le_of_aux_sum_gt` | ✅ |
| `Lower.lean` | `M_K` witness → `f_ge_log_frequently` | ✅ |

## How the lower bound works (`Lower.lean`)

Witness `n = M_K − 1` with `M_K = ∏_{p≤K, prime} p^{⌊log_p K⌋+1}`.
- `digit_le`: for prime `p≤K`, `k≤K`, every `i`: `k % pⁱ ≤ (M_K−1) % pⁱ`. Split at
  `a=⌊log_p K⌋+1`: for `i≤a`, `pⁱ ∣ M_K` ⟹ `(M_K−1)%pⁱ = pⁱ−1` maximal; for `i>a`,
  `k < pᵃ ≤ (M_K−1)%pⁱ`.
- `u_MK_eq_one`: the carry-free pattern ⟹ `v_p(C(n,k))=0` (`Legendre.factorization_choose_eq_zero`)
  ⟹ `u(M_K−1, k)=1` for all `k≤K`.
- `log_LK_le_psi`: `∑_{p≤K} ⌊log_p K⌋·log p ≤ ψ(K)` — the `O(K)` (not `O(K log K)`)
  cancellation, via the same von-Mangoldt-divisor-subsum trick as `log_centralBinom_le_psi`.
- `log_MK_le`: `log M_K = ψ(K)+θ(K) ≤ (2 log4 + 4)·K` via mathlib's `psi_le_const_mul_self` +
  `theta_le_log4_mul_x`.
- `f_ge_log_frequently`: `K < f(M_K−1)` because no `k≤K` is in the (nonempty, via
  `threshold_nonempty`) threshold set; combine with `log n ≤ C·K`.

**Refactor that enabled it** (commit `5e9eb6f`): the upper-bound averaging argument was split
so the witness `k` (with `n²<u n k`) is *exposed* (`Upper.exists_threshold_le`,
`Asymptotic.eventually_exists_threshold`), not just consumed. The lower bound needs
`threshold_nonempty` — else `f n = sInf ∅ = 0` and the bound is vacuous.

## Key decisions

- **Constant-relaxed, not sharp.** Sharp constants (`24/(π²−6)`, `1/2`) need PNT
  (`θ(x) ~ x`); we use only elementary Chebyshev bounds. Fully unconditional on mathlib.
- **`ChebyshevLower` built in-repo**: mathlib v4.29.1 ships θ/ψ *upper* bounds but no lower.

## Push status

Local commits on `master`, **not pushed** (box has no GitHub egress). Host-side `git push`.
Relevant commits: `5e9eb6f` (refactor), `517546f` (lower bound complete), `b9a6a8e` (handoff).

## Now-actionable: record #684 as formalized (host-side, both cloned locally)

The proof is done, so these two tracker PRs are now live next-steps. The proof lives in
**this repo**; trackers just point at it.
- **formal-conjectures** (`~/src/formal-conjectures`, DeepMind statement DB): #684 has no
  file → add `FormalConjectures/ErdosProblems/684.lean` with the faithful statement,
  `@[category research open]` (684 asks for the *exact order*; constant-relaxed bounds don't
  resolve it), and `@[formal_proof using lean4 at "<repo URL>"]`. Body stays `sorry` there by
  design (see their #728.lean pattern).
- **teorth/erdosproblems** (`~/src/erdosproblems`, `data/problems.yaml`): flip
  `formalized: no → yes`; `status` stays `open`.
- ⚠️ Note when PRing: ours is the **constant-relaxed** (`O((log n)²)` / `Ω(log n) i.o.`)
  result, not the sharp `24/(π²−6)` / `1/2` constants (those need PNT). Be honest about scope.
