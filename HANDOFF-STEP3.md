# HANDOFF — next session: finish the upper bound (step 3)

**Read `HANDOFF.md` first** for the full project context (objects, the verified scope
decision, recording trackers). This doc is the focused "start here" for the *remaining*
work: the analytic inequality that closes `f_le_polylog`.

**Repo**: `~/src/binomial-thresholds/` · mathlib **v4.29.1** · git `master`, commit when green.
Run inside the **lean-yolo-box** (`cd ~/src/lean-yolo-box && PROJECT_DIR=~/src/binomial-thresholds ./run.sh run`).

---

## 1. Where things stand (session 2 end)

The **entire upper bound is reduced to ONE inequality.** Everything below it is proven,
axiom-clean (`propext/Classical.choice/Quot.sound` only), 7 modules:

```
Legendre → CrucialObs → BlockCount → Upper(steps 1-2 + averaging) ;  Aggregation(R_j engine)
```

The one remaining goal is to supply `hbig` to `Upper.f_le_of_aux_sum_gt`:

```lean
-- PROVEN (Upper.lean): this reduces the whole upper bound to `hbig`.
theorem f_le_of_aux_sum_gt {n Y : ℕ} (hYn : Y ≤ n)
    (hbig : (2 : ℝ) * Y * Real.log n
      < ∑ p ∈ Nat.primesBelow (Y + 1),
          ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p) :
    f n ≤ Y
```

So the whole job is: **for `Y = ⌊C (log n)²⌋` and `n` large, prove the `hbig` inequality**,
then assemble `f_le_polylog` (the `∃ C, 0 < C ∧ ∀ᶠ n, f n ≤ C (log n)²` in `Basic.lean`)
by choosing `Y = ⌊C (log n)²⌋`, checking `Y ≤ n` eventually, and `f n ≤ Y ≤ C (log n)²`.

---

## 2. The toolbox (proven lemmas you'll build on)

All in namespace `BinomialThresholds`. Signatures are exact (copy-paste ready).

```lean
-- Aggregation.lean — the R_j engine:
theorem R_lower (P : Finset ℕ) (n M : ℕ) (hn : 0 < n) (hP : ∀ p ∈ P, p.Prime) :
    (M : ℝ) * (∑ p ∈ P, Real.log p)
        - Real.log ((n : ℝ) + M) * (∑ A ∈ Finset.range M, (A : ℝ))
      ≤ ∑ p ∈ P, ((p - n % p : ℕ) : ℝ) * Real.log p
-- (and the raw layer cake `sum_amul_log_ge` if you need a custom L)

-- CrucialObs.lean:
theorem sum_log_le_of_a_le {n A : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hA : ∀ p ∈ S, p - n % p ≤ A) :
    ∑ p ∈ S, Real.log p ≤ A * Real.log (n + A)

-- BlockCount.lean / Legendre.lean: already fully consumed by steps 1-2; unlikely needed again.
```

The number `aₚ := p − n%p`. Note the ℕ identity `p - 1 - n%p = (p - n%p) - 1` (`Nat.sub_right_comm`),
so the `hbig` summand `((p-1-n%p:ℕ):ℝ)·((Y/p-1:ℕ):ℝ)·log p` is `(aₚ−1)(⌊Y/p⌋−1) log p`.

---

## 3. NEXT TARGET — step 3a: the j-decomposition (combinatorial, NO analysis)

This is the clean, self-contained next lemma. Do it first; it needs no Chebyshev.

**Math.** Define `Pⱼ = {p prime ≤ Y : p·j ≤ Y}`. For prime `p ≤ Y`:
`⌊Y/p⌋ − 1 ≥ #{j ∈ [2,J] : p·j ≤ Y}` because `p·j ≤ Y ⟺ j ≤ ⌊Y/p⌋`
(`Nat.le_div_iff_mul_le`), so `{j ∈ [2,J] : p·j≤Y} = Icc 2 (min J ⌊Y/p⌋)`, of card
`min J ⌊Y/p⌋ − 1 ≤ ⌊Y/p⌋ − 1`. Since `(aₚ−1) log p ≥ 0`, multiply and swap sums:

```
∑_{p≤Y} (aₚ−1)(⌊Y/p⌋−1) log p  ≥  ∑_{p≤Y} (aₚ−1)·#{j∈[2,J]:p·j≤Y}·log p
                                =  ∑_{j=2}^J ∑_{p∈Pⱼ} (aₚ−1) log p   =  ∑_{j=2}^J (Rⱼ − Tⱼ)
```

**Suggested Lean statement** (keep the ℕ-cast form to match `hbig` exactly):

```lean
theorem j_decomposition {n Y J : ℕ} :
    ∑ j ∈ Finset.Icc 2 J,
        ∑ p ∈ (Nat.primesBelow (Y + 1)).filter (fun p => p * j ≤ Y),
          ((p - 1 - n % p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ Nat.primesBelow (Y + 1),
          ((p - 1 - n % p : ℕ) : ℝ) * ((Y / p - 1 : ℕ) : ℝ) * Real.log p
```

**Proof recipe** (mirror the `Upper.sum_card_log_le_sum_log_u` swap, which is the template):
1. Rewrite LHS inner filter-sum as an indicator over the fixed set `primesBelow(Y+1)`:
   `∑_{p∈Pⱼ} f p = ∑_{p∈primesBelow(Y+1)} if p·j ≤ Y then f p else 0` (`← Finset.sum_filter`,
   then the filter-set identity — note `p ∈ primesBelow(Y+1) ∧ p·j≤Y` already implies `p≤Y`).
2. `Finset.sum_comm` to swap `∑ⱼ ∑ₚ → ∑ₚ ∑ⱼ`.
3. Inner `∑_{j∈Icc 2 J} if p·j≤Y then (aₚ−1)log p else 0 = #{j∈Icc 2 J : p·j≤Y} • (aₚ−1)log p`
   (`← Finset.sum_filter`, `Finset.sum_const`, `nsmul_eq_mul`).
4. Termwise: `#{j∈Icc 2 J : p·j≤Y} ≤ Y/p − 1`, times nonneg `(aₚ−1)log p`
   (`mul_le_mul_of_nonneg_right`). For the card bound:
   `(Icc 2 J).filter(fun j => p*j≤Y) ⊆ Icc 2 (Y/p)` via `Nat.le_div_iff_mul_le hp.pos`
   (`p*j≤Y ⟺ j*p≤Y ⟺ j≤Y/p`), then `Nat.card_Icc : #(Icc a b) = b+1−a` gives
   `#(Icc 2 (Y/p)) = Y/p − 1`; finish with `Finset.card_le_card`.

⚠️ Watch the `p·j ≤ Y` vs `j·p ≤ Y` commute when applying `Nat.le_div_iff_mul_le`
(`a ≤ c/b ↔ a*b ≤ c`, so `j ≤ Y/p ↔ j*p ≤ Y`).

---

## 4. After 3a — the rest of `hbig` (heavier, analytic)

- **3b — per-j `Rⱼ` bound.** `∑_{p∈Pⱼ}(aₚ−1)log p = Rⱼ − Tⱼ` where
  `Rⱼ = ∑_{Pⱼ} aₚ log p`, `Tⱼ = ∑_{Pⱼ} log p`. Apply `R_lower Pⱼ n Mⱼ` with
  `Mⱼ = ⌊Y/(j·log n)⌋` (a ℕ — careful, `log n` is real; you likely want
  `Mⱼ = ⌊Y / (j * ⌈log n⌉)⌋` or carry `Mⱼ` as a real cutoff and re-derive. Decide the
  cleanest encoding early). Gives `Rⱼ ≥ Mⱼ·Tⱼ − log(n+Mⱼ)·∑_{A<Mⱼ}A`.

- **3c — Chebyshev on `Tⱼ`.** Need a LOWER bound `Tⱼ = ∑_{p≤Y/j} log p = θ(Y/j) ≥ (log2)(Y/j) − o`.
  mathlib has `Chebyshev.theta_eq_sum_primesLE_log` (`θ x = ∑_{p≤x} log p`) and the upper
  `theta_le_log4_mul_x`. **The lower bound `θ(x) ≥ (log2)·x − …` comes from
  `Chebyshev.two_pow_le_mul_lcmUpto`** (`2ⁿ ≤ (n+1)·lcmUpto n`) — chase how mathlib's
  Chebyshev file derives the lower θ bound (grep `theta` + `log 2` / `lcmUpto` in
  `Mathlib/NumberTheory/Chebyshev.lean`). ⚠️ reconcile `primesLE` (mathlib θ) vs
  `primesBelow` (our `Pⱼ`): `primesBelow (m+1)` = primes `≤ m` = `primesLE m`. There is
  almost certainly a bridge lemma; if not, prove a one-liner.

- **3d — asymptotic assembly.** Set `Y = ⌊C(log n)²⌋`, `C ≈ 16` (the verified relaxed
  constant — see `HANDOFF.md` scope section for the exact `C > 2/((log2−½)(π²/6−1))`
  derivation). Push the leading `(log n)³` term through `∑_{j=2}^J 1/j²`, choose `J` large
  enough that `C(log2−½)∑_{j≤J}1/j² > 2`, and absorb everything else into `o((log n)³)`.
  This is `Filter.atTop` / `IsLittleO` bookkeeping — the real grind. Expect this to be the
  bulk of the remaining effort; consider isolating each `o(1)` claim as its own lemma.

- **Final assembly** (`f_le_polylog` in `Basic.lean`): provide `C` (e.g. `17`), show
  `∀ᶠ n, …`: eventually `Y = ⌊C(log n)²⌋ ≤ n` (since `(log n)² = o(n)`), `0 < n`, `hbig`
  holds (3a–3d), so `f n ≤ Y ≤ C(log n)²` via `f_le_of_aux_sum_gt` + `Nat.floor_le`.

---

## 5. Box / build / commit mechanics

- Build a single module: `cd ~/src/binomial-thresholds && lake build BinomialThresholds.Aggregation`
  (always name the target + watch the job count ~8250; bare `lake build` prints "0 jobs").
- New file → add `import BinomialThresholds.<Name>` to `src/BinomialThresholds.lean`, then
  `lake build BinomialThresholds`.
- **Axiom check** (do before committing a finished lemma):
  write a scratch `src/BinomialThresholds/AxCheck.lean` with `import …` + `#print axioms <thm>`,
  run `lake env lean src/BinomialThresholds/AxCheck.lean`, expect
  `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`), then delete it.
- **Deletion in the box**: `trash` is NOT available (it's a macOS tool); `rm -f` works here
  (the host's block-rm hook is not active inside the container). Avoid leaving scratch files.
- **Commit when green** — reflexively, every passing lemma. `git` identity is set per-repo
  (`Trevor Morris <gotrevor@gmail.com>`). End messages with the `Co-Authored-By: Claude Opus 4.8`
  trailer. No remote yet; pushing is a separate confirm-first decision.

## 6. Gotchas banked this session

- `Real.log_prod` takes `s,f` **implicit**, only `hf` explicit: `Real.log_prod (fun p hp => …)`.
- Rewriting a predicate *inside* a `Finset.filter` hits "motive is not type correct" (Decidable
  instance in the motive). Use `Finset.filter_congr (fun x _ => …)` on the *sets* instead.
- `Real.log_pow (x) (n) : log (x^n) = n * log x` (x first). `Real.log_le_log (0<x) (x≤y)` exists
  (monotone, non-`iff`). `Real.log_nonneg (1≤x)`.
- `push_neg` is deprecated → use `push Not`.
- ℕ has no `mul_sub_one` (ring-only); use a `cases d`/`Nat.mul_succ` micro-lemma for `a*(d-1)`.
- `Nat.count_modEq_card` (exact residue count) is what made `BlockCount` sharper than the paper.
- In-box PDF with no poppler/pip: `python3` + `zlib` over the PDF's FlateDecode streams extracts
  text (decode kerned `TJ` arrays + octal glyph escapes). `refs/paper.pdf` is the source.
