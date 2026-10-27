# Explicit MVC counterexamples, proved in Lean

This repository proves facts about **specific exact polynomials** and shows that their strict violations extend to every sufficiently large degree. It does not formalize the research paper. No Python checker or external numerical report is used by the proofs.

Start with [`Mvc/Results.lean`](Mvc/Results.lean), which states the four public results.

## Results

Let $N$ be polynomial degree and $d=N-1$. Thus $d/(d+1)=(N-1)/N$.

| Result | Lean theorem |
|---|---|
| Every exact degree $N\ge2650$ has a counterexample to $(N-1)/N$ | `Mvc.Results.every_degree_ge_2650` |
| Every exact degree $N\ge2917$ has a counterexample to $1$ | `Mvc.Results.every_degree_ge_2917` |
| The stated degree-2650 polynomial beats $2649/2650$ at every critical point | `Mvc.Results.explicit_degree_2650` |
| The stated degree-2917 polynomial beats $1$ at every critical point | `Mvc.Results.explicit_degree_2917` |

The first two statements mean **there exists a counterexample at each degree**, not that every polynomial fails. If “above degree $a$” means strictly greater than $a$, use $a=2649$ and $b=2916$.

Degrees **2650** and **2917** are the smallest certified examples found in the source investigation. **Global minimality is not proved.** The last two theorems establish explicit witnesses, not the absence of lower-degree examples.

## What failure means

Normalize by $P(0)=0$ and $P'(0)=1$. Every critical point is then nonzero. Failure at threshold $T$ means

$$
\forall c\in\mathbb C,\quad P'(c)=0\implies\left|\frac{P(c)}c\right|>T.
$$

One large quotient is insufficient. Lean covers **every complex critical point**, including possible multiplicities. Writing $S(P)=\min_{P'(c)=0}|P(c)/c|$, the proved conservative bounds are

$$
S(P_{2650})>\frac{99964059}{100000000}>\frac{2649}{2650},
\qquad
S(P_{2917})>\frac{1000000129}{1000000000}>1.
$$

The guaranteed excesses are respectively $95127/5300000000$ and $129/1000000000$. The degree-2650 result is not claimed to exceed one, and the displayed targets are not asserted to equal the exact minima.

## The exact polynomials

Authoritative Lean definitions:

- [`Mvc.Data.degree2650`](Mvc/Data/Degree2650.lean): all 2649 exact critical centers.
- [`Mvc.Data.degree2917`](Mvc/Data/Degree2917.lean): all 2916 exact critical centers.
- [`Mvc.Witnesses.polynomial2650`](Mvc/Witnesses/Degree2650.lean).
- [`Mvc.Witnesses.polynomial2917`](Mvc/Witnesses/Degree2917.lean).

An entry `⟨a, b, m⟩ : RationalComplex` means exactly $c=a/m+i\,b/m$, with integer numerators and positive natural denominator. There are no floating-point tolerances. For the supplied list $c_1,\ldots,c_{N-1}$, define

$$
q_N(z)=\prod_{j=1}^{N-1}(z-c_j),\qquad
\boxed{P_N(z)=\frac1{q_N(0)}\int_0^z q_N(t)\,dt.}
$$

Equivalently,

$$
P_N(z)=\int_0^z\prod_{j=1}^{N-1}\left(1-\frac t{c_j}\right)dt
=\sum_{k=0}^{N-1}\frac{(-1)^k}{k+1}e_k(c_1^{-1},\ldots,c_{N-1}^{-1})z^{k+1},
$$

where $e_k$ is the elementary symmetric polynomial and $e_0=1$. The integral is coefficientwise polynomial antiderivation with zero constant term. This specifies every coefficient in $\mathbb Q(i)$ exactly.

Lean proves exact degree, both normalizations, and that the derivative vanishes **if and only if** the point occurs in the supplied list. No numerical rootfinder completeness assumption is used.

The original exact JSON coordinates under [`witnesses/`](witnesses/) are readable provenance. A pure Lean [transcription audit](Tools/AuditData.lean) compares them with the Lean literals by exact integer cross multiplication. The proofs use the literals directly and do not depend on JSON parsing or this audit.

## Why all higher degrees are covered

The fully proved [`Mvc.exists_degree_extension`](Mvc/Extension.lean) extends any strict normalized witness above $L\ge0$ to every higher exact degree $M$. Set

$$
Q_\epsilon(z)=P(z)+\epsilon z^M
$$

for sufficiently small nonzero $\epsilon$. At a critical point of $Q_\epsilon$,

$$
\frac{Q_\epsilon(c)}c=H(c),\qquad H(z)=\frac{P(z)}z-\frac{P'(z)}M.
$$

Since $M>\deg P\ge2$, $H$ is a nonconstant polynomial. The potentially bad set $\{|H|\le L\}$ is compact and contains no zero of $P'$. A sufficiently small perturbation keeps $Q_\epsilon'$ nonzero there. Therefore every new critical quotient still exceeds $L$.

The [mathematical explanation](docs/DEGREE_EXTENSION.md) gives the details. Lean proves compactness, perturbation, and exact degree; it assumes neither simplicity nor continuity of individually labeled roots.

Because $(M-1)/M$ rises with degree, one sub-one witness cannot cover the entire tail. Five **concrete Lean witnesses** give overlapping ranges:

| Degree | Strict lower bound | Covered degrees |
|---:|---:|---:|
| 2650 | $99964059/100000000$ | 2650–2782 |
| 2725 | $9996431/10000000$ | 2725–2801 |
| 2798 | $999649/1000000$ | 2798–2849 |
| 2840 | $249917/250000$ | 2840–3012 |
| 2917 | $1000000129/1000000000$ | Every degree from 2917 onward |

[`Coverage.lean`](Mvc/Coverage.lean) proves this arithmetic; [`Results.lean`](Mvc/Results.lean) supplies all five witness proofs. The final results have **no unproved witness or extension hypotheses**. Extension is existential: there is no table of expanded coefficients or computed rational perturbation sizes for infinitely many degrees.

## Build the proofs

The project pins Lean **4.28.0** and mathlib **v4.28.0**. Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

The first build computes five large certificates inside Lean and is heavier than checking the generic lemmas. For lower peak memory, use `sh check.sh` instead of the final `lake build`: it builds the five expensive witnesses sequentially, then checks the public results and prints the axiom audit. Cached builds are quick. No Python environment, Arb, numerical report, or external search program is required.

Inspect theorem dependencies and optionally audit data transcription:

```sh
lake env lean Mvc/AxiomAudit.lean
lake env lean --run Tools/AuditData.lean
```

[`Main.lean`](Main.lean) is an optional Lean-only diagnostic. Running it does **not** substitute for building the theorem files:

```sh
lake env lean --run Main.lean 2650 16000
```

## Proof architecture and trust

1. [`Polynomial.lean`](Mvc/Polynomial.lean) proves construction, normalization, exact degree, and exhaustive critical points.
2. [`Interval.lean`](Mvc/Interval.lean), [`ComplexBox.lean`](Mvc/ComplexBox.lean), and [`RationalComplex.lean`](Mvc/RationalComplex.lean) prove outward integer interval arithmetic sound.
3. [`Coefficients.lean`](Mvc/Coefficients.lean) connects coefficient lists, antiderivation, and Horner evaluation to mathematical polynomials.
4. [`Computation.lean`](Mvc/Computation.lean) implements the finite computation; [`Checker.lean`](Mvc/Checker.lean) proves that acceptance implies the all-critical strict bound, degree, and normalization.
5. [`Witnesses/`](Mvc/Witnesses/) proves acceptance for the actual data **inside Lean** and applies soundness.
6. [`Extension.lean`](Mvc/Extension.lean) and [`Coverage.lean`](Mvc/Coverage.lean) prove the all-degree consequences; [`Results.lean`](Mvc/Results.lean) closes the four statements.

The computation uses integer endpoints at scale $2^{16000}$. It encloses the unnormalized primitive $A(c)$ and $q(0)c$, then checks

$$
|A(c)|^2>T^2|q(0)c|^2
$$

with conservative lower and upper bounds. It does not divide by an uncertain complex interval. Lean proves that this comparison implies the required quotient inequality.

**Trust disclosure:** generic mathematics and checker soundness use standard Lean/mathlib axioms. Large acceptance proofs use **`native_decide`**, adding **`Lean.ofReduceBool` and `Lean.trustCompiler`**: the Lean compiler/runtime is trusted in addition to the kernel. This is not kernel-reduction-only computation. No Python result, custom numerical axiom, `sorry`, or admitted witness is used. [`AxiomAudit.lean`](Mvc/AxiomAudit.lean) exposes the final dependencies.

[`CheckerControls.lean`](Mvc/CheckerControls.lean) uses kernel `decide` on small end-to-end examples, including rejection at exact equality, a zero center, and a zero target denominator.

## Insight

The construction works backwards: choose the derivative’s roots, integrate, and improve the smallest critical quotient. The clover-like cloud is only a starting geometry. Adjusting selected factors affects the primitive globally, allowing critical values with surplus to help raise weaker values. Every finite change must still satisfy all critical inequalities.

Small coordinated shifts matter even when the outline barely changes, because

$$
\frac{q'(z)}{q(z)}=\sum_j\frac1{z-c_j}
$$

depends on all locations. The Lean proof does not assume this heuristic succeeds; it checks the final exact polynomial directly.

## Attribution

These are specific finite witnesses and their extension consequences, not a claim to the first disproof or a globally smallest example. Earlier work includes the [original Lean disproof](https://github.com/tadamcz/mean-value-problem) and [Jatar–Ng’s reformulation](https://arxiv.org/abs/2610.21472). Neither is imported to establish these numerical thresholds.

[provenance.json](provenance.json) identifies the preserved exact inputs. All proof dependencies are included here or in pinned mathlib. No research paper is included.
