# arXiv:2603.29961 — §2 reference (binomial-thresholds)

> **Source:** "Short proofs in combinatorics and number theory"
> Boris Alexeev, Moe Putterman, Mehtaab Sawhney, Mark Sellke, Gregory Valiant.
> arXiv:2603.29961v1 [math.CO] [math.NT]. <https://arxiv.org/abs/2603.29961>
>
> **Note:** This is a *math-content* extraction of §2 for the Lean formalization,
> not a verbatim copy of the paper. The box has no local internet; this was
> pulled server-side via WebFetch (which returns processed markdown, not the
> PDF). For the canonical PDF, fetch `https://arxiv.org/pdf/2603.29961` from a
> networked machine. Statements/constants below are paraphrased from the HTML
> version — **verify against the real PDF before trusting any constant.**

## Paper abstract (verbatim)

> We give a triplet of short proofs, each of which answers a question raised by
> Erdős. The first concerns the small prime factors of $\binom{n}{k}$, the
> second concerns whether an additive basis $A$ can always be split into pieces
> $A_1$ and $A_2$ such that each of $A_i + A_i$ has bounded gaps, and the final
> concerns whether $\{\alpha p\}$ is "well-distributed" in the sense introduced
> by Hlawka and Petersen. In each case, the proof is due entirely to an internal
> model at OpenAI.

§2 is the first of the triplet (Erdős #684, small prime factors of $\binom{n}{k}$).

## (1) Definition of f(n)

For integers $0 \le k \le n$, define
$$u(n,k) = \prod_{p \le k} p^{v_p\binom{n}{k}}$$
where $v_p\binom{n}{k}$ is the exponent of prime $p$ in $\binom{n}{k}$. Then
$$f(n) = \min\{\, 0 \le k \le n : u(n,k) > n^2 \,\}.$$

## (2) Upper bound — Theorem 2.1

For sufficiently large $n$,
$$f(n) \le \left(\frac{24}{\pi^2-6} + o(1)\right)(\log n)^2 \le 6.20219\,(\log n)^2.$$
Order: $O((\log n)^2)$ (polylogarithmic).

## (3) Lower bound — Theorem 2.1

There is an infinite sequence $n_j \to \infty$ with
$$f(n_j) \ge \left(\tfrac12 + o(1)\right)\log n_j.$$
Order: $\Omega(\log n)$ infinitely often.

## (4) Key lemmas

**Legendre / Kummer valuation.** For prime $p$,
$$v_p\!\binom{n}{k} = \sum_{t \ge 1}\left(\left\lfloor\tfrac{n}{p^t}\right\rfloor
  - \left\lfloor\tfrac{n-k}{p^t}\right\rfloor - \left\lfloor\tfrac{k}{p^t}\right\rfloor\right),$$
with the simple lower bound (carry indicator)
$$v_p\!\binom{n}{k} \ge \mathbb{1}[\,n \bmod p < k \bmod p\,].$$

## (5) Proof outlines

### Upper bound
- Set $Y = \lfloor C(\log n)^2\rfloor$, $C = \tfrac{24}{\pi^2-6} + \varepsilon$.
- Partition primes $p \le Y$ into $\mathcal P_j = \{p : p \le Y/j\}$, $j \ge 2$.
- For each prime $p$ set $a_p = p - (n \bmod p)$.
- **Key inequality:** if $a_p \le A \le M_j$ with $M_j = \lfloor Y/(j\log n)\rfloor$,
  then $p \mid$ one of $n+1,\dots,n+A$, giving
  $$\sum_{p \in \mathcal P_j,\, a_p \le A} \log p \le A(\log n + \log M_j).$$
- Aggregate over $A$: $R_j := \sum_{p \in \mathcal P_j} a_p \log p
  \ge \tfrac{C^2}{2j^2}(\log n)^3 - o((\log n)^3)$.
- Sum over $j = 2,\dots,J$ using $\sum_{j\ge2} j^{-2} = \pi^2/6 - 1$ and PNT.
- Averaging shows some $k \le Y$ has $u(n,k) > n^2$.

### Lower bound
- $M_K = \prod_{p \le K} p^{\lfloor \log_p K\rfloor + 1}$, threshold $K \ge 2$.
- Show for all $0 \le k \le K$ and prime powers $p^a$:
  $(M_K - 1) \bmod p^a \ge k \bmod p^a$.
- Legendre $\Rightarrow v_p\binom{M_K-1}{k} = 0$ for all $p \le K$, $k \le K$.
- Hence $u(M_K-1, K) = 1 \not> (M_K-1)^2$, so $f(M_K-1) > K$.
- PNT: $\log M_K = 2K + o(K)$, so $f(M_K-1) \ge \tfrac12\log(M_K-1)$ i.o.
