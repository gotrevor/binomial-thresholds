# HANDOFF — binomial-thresholds formalization

**Repo**: `~/src/binomial-thresholds/` · **Started**: 2026-05-30 · **mathlib**: v4.29.1
**Build**: green — `Basic` (2 expected `sorry`s) + `Legendre` (0 `sorry`, axiom-clean).

## TL;DR state

`src/BinomialThresholds/Basic.lean`: the faithful objects `u`, `f` and two
**constant-relaxed** theorem statements, both still `sorry`.

`src/BinomialThresholds/Legendre.lean`: ✅ **the atomic building block, fully proven**
(Opus session 2, 2026-05-30). Two lemmas, both axiom-clean (`propext, Classical.choice,
Quot.sound` only — no `sorryAx`):
- `one_le_factorization_choose` : `p.Prime → k ≤ n → n % p < k % p → 1 ≤ vₚ(C(n,k))`
  (the carry indicator lower bound the **upper** bound sums over `k`).
- `factorization_choose_eq_zero` : `p.Prime → k ≤ n → (∀ i, k % pⁱ ≤ n % pⁱ) → vₚ(C(n,k)) = 0`
  (the carry-free pattern the **lower** bound's witness family is built to hit).
- shared helper `m_le_mod_add_mod_iff (hm : 0 < m) (hkn : k ≤ n) :`
  `m ≤ k%m + (n-k)%m ↔ n%m < k%m` — the base-`m` single-digit carry ⟺ borrow fact.
  (⚠️ the iff is FALSE at `m = 0`; needs `0 < m`. Built both lemmas off `factorization_choose`
  from `Mathlib/Data/Nat/Choose/Factorization.lean`, NOT `dvd_choose` — `dvd_choose` needs
  BOTH `k<p` and `n-k<p`, too restrictive for general `k`.)

mathlib pinned to v4.29.1 (Trevor's everywhere-else version) so the 1.6G local cache is
reused — `lake exe cache get` was an instant hit (8229 oleans, no download).

## What & why

Formalizing **§2 of Alexeev–Putterman–Sawhney–Sellke–Valiant, "Short proofs in
combinatorics and number theory"** ([arXiv:2603.29961](https://arxiv.org/abs/2603.29961),
Apr 2026 — the OpenAI "short proofs" series; proofs found by an internal model).
Answers the order-of-growth side of an Erdős question on small prime factors of
`C(n,k)` ([erdosproblems.com/684](https://www.erdosproblems.com/684)).

**Chosen as the deliberate anti-`sum-product` pick.** sum-product is "too hard" not
because the math is deep but because the proof bottoms out in machinery mathlib
lacks (Martinet class-field towers, Blichfeldt/Hensley/Brauer–Siegel) → permanently
conditional on axioms. This was selected by triaging the OpenAI short-proofs papers
I & II for "self-contained, every dependency already in mathlib." (Paper I §3
Burr–Erdős basis #741 was the other gem but DeepMind's prover fully formalized it
Apr 2026; §4 + all of paper II route through Maynard–Tao / Hayman / Pollack /
elliptic-curve machinery = same wall, rejected.)

## The objects (Basic.lean)

```
u n k = ∏_{p ∈ primesBelow (k+1)} p ^ (Nat.choose n k).factorization p   -- ∏_{p≤k} p^{vₚ(C(n,k))}
f n   = sInf { k | n^2 < u n k }                                          -- min{ k : u(n,k) > n² }
```
Sanity (by hand): `u 10 3 = 2³·3 = 24` since `C(10,3)=120=2³·3·5`, primes ≤ 3 = {2,3}.
NOT vacuous. `f` is `noncomputable` (sInf); `sInf ∅ = 0`, so `f_le_polylog`'s content
also certifies the witness set is eventually nonempty.

## ⚠️ THE SCOPE DECISION (read before touching constants)

The paper's **sharp** constants — `f(n) ≤ (24/(π²−6)+o(1))(log n)² ≤ 6.20219(log n)²`
upper, `f(nⱼ) ≥ (1/2+o(1))log nⱼ` lower — come from `θ(x) ~ x`, i.e. the **Prime
Number Theorem asymptotic**, which is **NOT in mathlib** (that is precisely what the
PrimeNumberTheorem+ project supplies; PNT+ is on v4.29.0 → importing it forks the
cache and drags a research project in as a dep).

So we deliberately target the **constant-relaxed** statements and stay unconditional:
- `f_le_polylog`        : `∃ C>0, ∀ᶠ n, (f n) ≤ C·(log n)²`
- `f_ge_log_frequently` : `∃ c>0, ∃ᶠ n, c·log n ≤ (f n)`

### ✅ Scope decision VERIFIED on paper (Opus session 2)

Worked the paper's upper-bound argument through with Chebyshev `θ(x) ≍ x` substituted
for the PNT `θ(x) ~ x`, to confirm the relaxed statement actually survives (it's not
enough that the *statement* is weaker — the *proof* has to go through on what mathlib has):

- Paper's `R_j ≥ M_j·T_j − ½M_j²(log n + log M_j)`. With `M_j = Y/(j log n)`,
  `Y = C(log n)²`, both terms are `Θ((log n)³/j²)`. PNT gives `T_j ~ Y/j` (coeff 1) ⟹
  `R_j ≥ (C²/2j²)(log n)³`. **Chebyshev** gives only `T_j ≥ (log 2)·Y/j` ⟹
  `R_j ≥ (C²/j²)(log 2 − ½)(log n)³`. The `log 2 − ½ ≈ 0.193 > 0` is what saves it —
  Chebyshev's lower constant `log 2 ≈ 0.693` clears the `½` from the `∑A ≈ M_j²/2`.
- Averaging needs `C·(log 2 − ½)·∑_{j≥2} j⁻² > 2`, i.e.
  `C > 2 / ((log 2 − ½)(π²/6 − 1)) ≈ 2 / (0.193·0.645) ≈ 16.06`.
- The subtracted `∑ T_j = O(Y log log n) = o(Y log n)` (Chebyshev upper `θ ≤ log 4·x`), lower order.

**So the relaxed upper bound holds with `C ≈ 16` (vs the sharp `6.20219`), zero axioms.**
The lower bound similarly survives: `log M_K = ψ(K) ∈ [c₁K, c₂K]` by Chebyshev ⟹
`f(M_K−1) > K ≥ c·log(M_K−1)` for some `c > 0`. The HANDOFF's central bet is sound.

These need only the **elementary Chebyshev bounds**, which mathlib v4.29.1 ships in
`Mathlib.NumberTheory.Chebyshev` (verified present this session):
| lemma | role |
|-------|------|
| `Chebyshev.theta_eq_sum_primesLE_log` | `θ x = ∑_{p≤x} log p` — **the paper's `Tⱼ` sum** |
| `Chebyshev.theta_le_log4_mul_x` | `θ x ≤ log 4 · x` — relaxed upper (replaces θ~x) |
| `Chebyshev.two_pow_le_mul_lcmUpto` | `2^n ≤ (n+1)·lcmUpto n` — lower-bound engine |
| `Chebyshev.psi_le_const_mul_self`, `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` | ψ≍x, ψ≈θ |

Same honest move as sum-product's `card_boxAdd_le` (constant relaxed `(2X+1)ᵈ→(2X+2)ᵈ`).
**Do not** "improve" to the sharp constants — that reintroduces the exact PNT wall
this project was chosen to avoid. Sharp constants = optional hard-mode only.

## Proof spine (next session: do the upper bound first)

`f_le_polylog` is the meatier one and carries the paper's cleverness.

1. ✅ **Legendre building block — DONE** (`Legendre.lean`, axiom-clean). Both the
   `≥ 1` lower bound (`one_le_factorization_choose`) and the `= 0` no-carry companion
   (`factorization_choose_eq_zero`) are proven off mathlib's `Nat.factorization_choose`
   (carries = `#{i ∈ Ico 1 b | pⁱ ≤ k%pⁱ + (n−k)%pⁱ}`). The `1_{n mod p < k mod p}`
   indicator is the `i=1` term; lower bound = "that term is in the set", zero = "no
   term is". Shared digit-carry iff is `m_le_mod_add_mod_iff`.
2. **Sum over k**: `∑_{k=1}^Y log(u(n,k)) ≥ ∑_{p≤Y}(⌊Y/p⌋−1)(aₚ−1)log p` where
   `aₚ = p − (n mod p)`; recognize the prime sums via `theta_eq_sum_primesLE_log`.
3. **Pigeonhole / averaging**: with `Y = ⌊C(log n)²⌋`, at least one `k ≤ Y` has
   `u(n,k) > n²`, so `f n ≤ Y`. Relaxed `C` from `theta_le_log4_mul_x`, not θ~x.

`f_ge_log_frequently`: witness `n = (∏_{p≤K} p^{⌊log_p K⌋+1}) − 1`; for `k≤K`,
`n mod pᵃ ≥ k mod pᵃ` ⟹ `vₚ(C(n,k))=0` for all `p≤K` ⟹ `u(n,k)=1 ≤ n²`, so
`f n > K`. `log n = log(M_K) = ψ(K)+θ(K) = Θ(K)` via Chebyshev ⟹ `f n ≥ c log n`.

## Build / cache gotchas (carried from sum-product)

- `lake build` with **no target** prints "0 jobs" even if nothing compiled. Always
  build the explicit target `lake build BinomialThresholds` and watch the job count
  (~8250 here). `lakefile.toml` uses package-level `srcDir = "src"`.
- A `sorry` of a *false/vacuous* statement is worse than nothing — sanity-check every
  statement says what the paper means (the `u 10 3 = 24` check above).
- `~/src/mathlib4` is a local checkout (currently v4.30.0-rc2, close enough to grep
  lemma names; confirm signatures against v4.29.1 if a build fails).
- Use `trash`, not `rm` (hook blocks `rm`). Git repo initialized (baseline
  `2c6200a`, branch `master`, identity `Trevor Morris <gotrevor@gmail.com>`).
  Commit green builds reflexively — see KB `feedback_commit_when_green.md`. No
  remote yet; pushing anywhere public is a separate, confirm-first decision.

## Recording it when proven (two trackers, NEITHER hosts the proof)

Both cloned locally this session. The proof lives in **this repo**; trackers just point.
- **formal-conjectures** (`~/src/formal-conjectures`, DeepMind statement DB): #684 has
  no file yet → PR a new `FormalConjectures/ErdosProblems/684.lean` with the faithful
  statement, tag `@[category research open]` (684 asks for the *exact order*; bounds
  don't resolve it), and once proven add `@[formal_proof using lean4 at "<repo URL>"]`.
  Theorem body stays `sorry` there by design (see their #728.lean for the pattern).
- **teorth/erdosproblems** (`~/src/erdosproblems`, website DB `data/problems.yaml`):
  PR flips `formalized: no → yes` (it's currently `no`); `status` stays `open`.
