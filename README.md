# Explicit counterexamples to Smale’s mean value conjecture

This repository has one purpose: specify exact counterexample polynomials, check every critical point, and prove that counterexamples exist in every sufficiently large degree. It contains no research paper or search machinery.

**Proof status:** the results below have mathematical proofs supported by exhaustive, outward-rounded interval certificates. They are **not yet formalized in the Lean theorem prover**. See [verification and trust](#verification-and-trust). “Smallest known” below means smallest certified in the source investigation, not a worldwide record or a proof of global minimality.

## The four results

Use $N$ for the polynomial’s degree and $d=N-1$ for the number of critical points counted with multiplicity. Thus your bound $d/(d+1)$ is $(N-1)/N$.

| Claim | Result | Scope |
|---|---|---|
| Counterexamples in every sufficiently large degree to $d/(d+1)$ | **Every $N\ge2650$** has a counterexample | Existence at each exact degree; not a claim about every polynomial |
| Counterexamples in every sufficiently large degree to $1$ | **Every $N\ge2917$** has a counterexample | Existence at each exact degree |
| Smallest certified degree found breaking $d/(d+1)$ | **$N=2650$**, so $d=2649$ | Lower degrees have not been ruled out |
| Smallest certified degree found breaking $1$ | **$N=2917$**, so $d=2916$ | Lower degrees have not been ruled out |

If “above degree $a$” means strictly greater than $a$, the first two statements use $a=2649$ and $b=2916$. Equivalently, the inclusive thresholds are $2650$ and $2917$.

The global smallest degrees remain unknown. This repository does **not** claim to prove global minimality for the last two rows.

## What failure means

Normalize a complex polynomial by $P(0)=0$ and $P'(0)=1$, and define

$$
S(P)=\min_{P'(c)=0}\left|\frac{P(c)}c\right|.
$$

No critical point is zero, because $P'(0)=1$. Failure at a threshold $T$ means **every** critical point has $|P(c)/c|>T$. One large critical quotient is not enough.

For degree $2650$, the exact witness satisfies

$$
S(P_{2650})>\frac{99964059}{100000000}
=0.99964059
>\frac{2649}{2650}.
$$

Its guaranteed excess over the degree-dependent bound is

$$
\frac{99964059}{100000000}-\frac{2649}{2650}
=\frac{95127}{5300000000}>0.
$$

This witness has a critical quotient below $1$: it breaks only the degree-dependent bound.

For degree $2917$, the exact witness satisfies

$$
S(P_{2917})>\frac{1000000129}{1000000000}
=1.000000129>1.
$$

It breaks both bounds. These are conservative strict lower bounds, not assertions that the minima equal those decimals.

## The exact polynomials

The complete exact inputs are:

- [Degree 2650: 2649 critical centers](witnesses/2650/critical_centers.json).
- [Degree 2917: 2916 critical centers](witnesses/2917/critical_centers.json).

Each JSON row has the form `[[a,b],[u,v]]`, meaning precisely $c=a/b+i\,u/v$. The integers are exact; there is no rounding convention or missing tolerance. All centers are nonzero. For either file, let $c_1,\ldots,c_{N-1}$ be its listed centers and define

$$
\boxed{\quad P_N(z)=\int_0^z\prod_{j=1}^{N-1}\left(1-\frac{t}{c_j}\right)\,dt.\quad}
$$

The integral is the polynomial primitive with constant coefficient zero. Equivalently, with $e_k$ the elementary symmetric polynomial and $e_0=1$, its coefficients are exactly

$$
P_N(z)=\sum_{k=0}^{N-1}
\frac{(-1)^k}{k+1}
 e_k(c_1^{-1},\ldots,c_{N-1}^{-1})z^{k+1}.
$$

This specifies every coefficient in $\mathbb Q(i)$ without printing a large, poorly conditioned expanded coefficient list. It is a complete exact polynomial definition, not merely a picture of approximate critical points.

Differentiating gives

$$
P_N'(z)=\prod_{j=1}^{N-1}(1-z/c_j).
$$

Therefore its exact degree is $N$, its normalization is automatic, and its critical multiset is **exactly the supplied list**. Root completeness is algebraic, not a numerical rootfinder claim. The remaining computational assertion is the strict inequality at each of these known points.

## Why every larger degree is covered

A strict witness above a fixed threshold $L$ can be extended to any higher degree $M$ by adding $\epsilon z^M$ with a sufficiently small nonzero $\epsilon$. The [complete degree-extension proof](docs/DEGREE_EXTENSION.md) uses the identity

$$
\frac{(P+\epsilon z^M)(c)}c
=\frac{P(c)}c-\frac{P'(c)}M
\qquad\text{when }(P+\epsilon z^M)'(c)=0.
$$

The right side is a fixed polynomial in $c$. All potentially bad critical locations lie in a compact set where $P'$ has no zeros; sufficiently small perturbations cannot introduce a critical point there. This proves strict extension, including repeated critical points.

Since the bound $(M-1)/M$ rises with $M$, the degree-2650 witness alone does not cover the entire tail. Five exact witnesses bridge the gap:

| Witness | Strict certified lower bound | Degrees whose bound it beats after extension |
|---|---:|---:|
| [2650](witnesses/2650/) | $99964059/100000000$ | $2650$–$2782$ |
| [2725](witnesses/2725/) | $9996431/10000000$ | $2725$–$2801$ |
| [2798](witnesses/2798/) | $999649/1000000$ | $2798$–$2849$ |
| [2840](witnesses/2840/) | $249917/250000$ | $2840$–$3012$ |
| [2917](witnesses/2917/) | $1000000129/1000000000$ | Every $M\ge2917$ |

These intervals overlap and cover every integer $M\ge2650$. The last witness exceeds $1$ and supplies the constant-one tail by itself. The extension is an existence proof; we do not provide an expanded polynomial or a computed safe $\epsilon$ for every intermediate degree.

## Insight into the construction

The method works backwards from critical points. It chooses the derivative’s roots first, integrates, and then tries to raise the **smallest** critical quotient. This makes checking completeness unusually simple: there can be no undiscovered critical point outside the plotted cloud.

The degree-2650 witness arose from a clover-like distribution of critical points, followed by adjustments to selected derivative factors. Some critical values had surplus above the minimum. Moving their factors changed the primitive globally, allowing weaker critical values to rise while the moved values remained acceptable. A successful update must check both the retained and moved critical points; a favorable linear prediction alone is insufficient.

The visible outline is not the entire mechanism. For $q=P'$, the positions influence the whole logarithmic derivative,

$$
\frac{q'(z)}{q(z)}=\sum_j\frac1{z-c_j}.
$$

Small coordinated shifts can change this field even when the cloud still looks like the same clover. The final certificate is independent of that discovery story: only the exact centers and exhaustive quotient inequalities enter the proof.

## Reproduce the certificates

The recorded verification environment is Python 3.9.6 with `python-flint==0.6.0`. From this repository’s root:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python scripts/verify.py
```

The last command reconstructs all five polynomials, verifies all **13,925 critical quotients**, and checks the overlapping ranges using exact rational arithmetic. It reads no files from the research repository and does not rely on stored `PASS` flags.

To check one witness or write fresh full reports:

```sh
.venv/bin/python scripts/verify.py --degree 2650
.venv/bin/python scripts/verify.py --degree 2917 --bits 48000
.venv/bin/python scripts/verify.py --output verification/fresh/run1
```

An output directory must be new. A low-precision failure means the requested inequality was not certified at that precision, not that the exact witness has been disproved. The committed fresh run is in [verification/release](verification/release/); original preserved reports accompany each witness for provenance.

## Verification and trust

The checker uses Arb through `python-flint` for outward-rounded complex ball arithmetic. It explicitly checks exact input hashes, nonzero centers, degree and multiset count, finite intermediate results, a nonzero normalizing constant, and strict comparison of every quotient modulus with the exact rational target. Serialized reports must retain both enclosure and strictness. See the [internal verification audit](docs/VERIFICATION_AUDIT.md).

The proof depends on these arithmetic and program checks. It is **not** a Lean-kernel proof, an external peer review, or a proof that no lower-degree example exists. A full Lean formalization would need to prove the certificate checker sound and verify the exact data, as well as formalize the extension lemma. An imported Boolean `verified = true` would not do that.

## Attribution and provenance

These are specific finite-degree witnesses from the MVC investigation, not a claim to the first disproof of Smale’s conjecture. Earlier work includes the [original Lean disproof repository](https://github.com/tadamcz/mean-value-problem) and [Jatar–Ng’s analytic reformulation](https://arxiv.org/abs/2610.21472). This repository does not import their proofs as evidence for its numerical degree thresholds.

[provenance.json](provenance.json) records the original input paths and hashes. Those paths describe provenance only; all files required by the checker are included here. No research paper is included.
