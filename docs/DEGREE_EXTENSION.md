# Counterexamples in every sufficiently large degree

This note proves the degree-extension step and the exact arithmetic covering argument. The five starting witnesses are computer-assisted exact polynomials; their exhaustive critical-value certificates are a separate input. This is a mathematical proof, not a Lean theorem-prover formalization.

For a complex polynomial $P$ of exact degree $n\ge2$, normalized by $P(0)=0$ and $P'(0)=1$, define

$$
S(P)=\min_{P'(c)=0}\left|\frac{P(c)}c\right|.
$$

Every critical point is nonzero because $P'(0)=1$. There are $n-1$ critical points counted with multiplicity. The degree-dependent comparison is $(n-1)/n$; the ordinary comparison is $1$.

## Strict degree extension

**Lemma.** Suppose $P$ has exact degree $n\ge2$, $P(0)=0$, $P'(0)=1$, and $S(P)>L$ for a real number $L\ge0$. For every integer $N>n$, there is $\delta>0$ such that every complex $\epsilon$ with $0<|\epsilon|<\delta$ gives an exact-degree-$N$ polynomial

$$
Q_\epsilon(z)=P(z)+\epsilon z^N
$$

satisfying $Q_\epsilon(0)=0$, $Q_\epsilon'(0)=1$, and $S(Q_\epsilon)>L$.

**Proof.** Since $P(0)=0$, the expression $P(z)/z$ extends to a polynomial. Define the polynomial

$$
H(z)=\frac{P(z)}z-\frac{P'(z)}N.
$$

If $a_n\ne0$ is the leading coefficient of $P$, the coefficient of $z^{n-1}$ in $H$ is

$$
a_n\left(1-\frac nN\right)\ne0.
$$

Thus $H$ is a nonconstant polynomial of exact degree $n-1$. Its bounded sublevel set

$$
E=\{z\in\mathbb C:|H(z)|\le L\}
$$

is compact: it is closed, and $|H(z)|\to\infty$ as $|z|\to\infty$.

The derivative $P'$ has no zero in $E$. Indeed, if $P'(c)=0$, then $c\ne0$ and

$$
|H(c)|=\left|\frac{P(c)}c\right|\ge S(P)>L.
$$

If $E$ is nonempty, compactness gives finite constants

$$
A=\min_{z\in E}|P'(z)|>0,
\qquad
B=\max_{z\in E}N|z|^{N-1}\ge0.
$$

Take $\delta=A/(B+1)$. Whenever $|\epsilon|<\delta$, every $z\in E$ satisfies

$$
|Q_\epsilon'(z)|
=|P'(z)+\epsilon Nz^{N-1}|
\ge A-|\epsilon|B>0.
$$

Hence all critical points of $Q_\epsilon$ lie outside $E$. If $E$ is empty, the same conclusion holds without any restriction on $\epsilon$; take $\delta=1$.

At a critical point $c$ of $Q_\epsilon$, normalization gives $c\ne0$ and the critical equation gives

$$
\epsilon Nc^{N-1}=-P'(c).
$$

Consequently the exact identity

$$
\frac{Q_\epsilon(c)}c
=\frac{P(c)}c+\epsilon c^{N-1}
=\frac{P(c)}c-\frac{P'(c)}N
=H(c)
$$

implies $|Q_\epsilon(c)/c|>L$. This holds for **every** critical point, including repeated critical points. Their finite minimum is therefore strictly greater than $L$. Finally, $\epsilon\ne0$ and $N>n$ give exact degree $N$, and $N\ge3$ preserves the normalization. This proves the lemma. $\square$

This proof does not assume continuity or simplicity of individual critical roots and does not require a census of escaping roots. The polynomial $H$ identifies all potentially bad critical locations in a fixed compact set, where a small derivative perturbation cannot create a critical point.

For $N=n$, simply retain $P$. Thus a strict witness above $L$ in degree $n$ supplies strict witnesses above the same $L$ in every degree $N\ge n$. The lemma is existential: it specifies an admissible radius through compact extrema, but does not calculate a rational $\epsilon$ or expanded coefficients for every $N$.

## Five exact starting witnesses

Each witness is specified by a complete list of nonzero Gaussian-rational critical centers $c_1,\ldots,c_{n-1}$, with multiplicities allowed, through

$$
P'(z)=\prod_{j=1}^{n-1}\left(1-\frac z{c_j}\right),
\qquad
P(z)=\int_0^z P'(t)\,dt.
$$

This formula proves exact degree, normalization, and critical completeness without a numerical rootfinder. The preserved interval certificates check every critical quotient against the exact rational target in the table.

| Degree $n$ | Certified strict target $L$ | Local exact witness | Degrees covered by the target |
|---:|---:|---|---:|
| $2650$ | $99964059/100000000$ | [`witnesses/2650/`](../witnesses/2650/) | $2650\le N\le2782$ |
| $2725$ | $9996431/10000000$ | [`witnesses/2725/`](../witnesses/2725/) | $2725\le N\le2801$ |
| $2798$ | $999649/1000000$ | [`witnesses/2798/`](../witnesses/2798/) | $2798\le N\le2849$ |
| $2840$ | $249917/250000$ | [`witnesses/2840/`](../witnesses/2840/) | $2840\le N\le3012$ |
| $2917$ | $1000000129/1000000000$ | [`witnesses/2917/`](../witnesses/2917/) | Every $N\ge2917$ |

All five exact inputs and a standalone checker are included in this repository. These targets are strict lower bounds, not claims that the minima equal the listed fractions.

## Exact range arithmetic

For $L<1$,

$$
L>\frac{N-1}N
\quad\Longleftrightarrow\quad
N(1-L)<1.
$$

The first four targets satisfy this strict inequality through their tabulated upper endpoints. The endpoint products, using integers only, are

$$
\begin{aligned}
2782\cdot35941&=99987862<100000000,\\
2801\cdot3569&=9996769<10000000,\\
2849\cdot351&=999999<1000000,\\
3012\cdot83&=249996<250000,
\end{aligned}
$$

The corresponding products at $2783$, $2802$, $2850$, and $3013$ exceed their respective denominators, so the four displayed finite ranges are the maximal ranges obtained by comparing these targets strictly with $(N-1)/N$.

The intervals overlap: the second starts at $2725\le2782$, the third at $2798\le2801$, the fourth at $2840\le2849$, and the final infinite interval starts at $2917\le3012$. Their union therefore contains every integer $N\ge2650$.

**Theorem (using the five certified inputs).** For every integer $N\ge2650$, there exists an exact-degree-$N$ normalized complex polynomial $P$ such that

$$
S(P)>\frac{N-1}N.
$$

For every integer $N\ge2917$, there exists such a polynomial with

$$
S(P)>1.
$$

**Proof.** Choose a row whose interval contains $N$. Apply strict degree extension to its certified witness and target $L$, or use the witness unchanged if $N$ is its original degree. For the first four rows, the exact arithmetic above gives $S(P)>L>(N-1)/N$. In the last row, $L=1+129/10^9>1>(N-1)/N$, and the same extension also proves the ordinary assertion. $\square$

No smallest failing degree, global optimality, or ordinary counterexample below degree $2917$ is asserted. The conclusion for all degrees is a theorem from the five exhaustive certificate inputs and the extension lemma; it is not a finite table of coefficients for all degrees.

## Provenance and verification boundary

The range data agree with `../mvc/findings/degree_bound_all_large_degrees.txt` and `../mvc/investigation/experiments/new_model_degree2650_all_large_range_check.json`. The original degree-extension discussion is in `../mvc/findings/degree_monotonicity.txt`; the compact-sublevel proof above supplies the strict-margin conclusion directly, without appealing to individual root convergence.

The five interval-verification bundles are computer-assisted mathematical evidence, not Lean kernel proofs. No axiom or placeholder turns them into a theorem-prover proof here. A future formalization must verify both those witness inputs and the analytic extension lemma, or clearly display them as hypotheses.
