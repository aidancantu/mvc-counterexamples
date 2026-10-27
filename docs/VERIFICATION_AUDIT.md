# Verification audit

This is an internal mathematical and code audit of the compact certificate repository. It is not a Lean theorem-prover proof, external peer review, or a global minimum-degree claim.

## Evidence checked independently

- All five copied `config.json` and `critical_centers.json` files are byte-for-byte identical to their preserved source bundles in the sibling research repository.
- The source reports have matching input/config/verifier hashes, the exact required counts, and finite exported Arb intervals strictly exceeding their exact rational targets. This aggregation was independently rerun for all five witnesses.
- The smallest preserved certified degree-dependent witness is 2650; the smallest preserved constant-one witness is 2917. These are records of this investigation, not exclusions of smaller degrees.

## Standalone verifier: static review passed

`scripts/verify.py` reconstructs the polynomial from exact rational centers and does not trust saved success flags or a numerical rootfinder. With the monic product $q(z)=\prod_j(z-c_j)$, it constructs $P=\int q/q(0)$. Nonzero centers imply $q(0)\ne0$, exact degree and normalization follow algebraically, and the supplied multiset contains every derivative zero, including multiplicity.

All numerical stages check finiteness: centers, derivative coefficients, primitive coefficients, critical evaluations, quotients, magnitudes, and exported intervals. The checker requires the exact expected target and count, nonzero normalization, strict lower bounds, and containment after serialization. Reports therefore connect the exact input polynomial to every critical quotient. They remain computer-assisted Arb certificates, not kernel proofs.

The strict coverage endpoint calculation is correct. The five ranges are 2650–2782, 2725–2801, 2798–2849, 2840–3012, and 2917 onward. They overlap. Coverage is printed by the CLI only after the requested full five-witness recomputation succeeds.

## Safeguard controls actually run

The fresh verifier rejects each of these inputs:

- NaN, positive infinity, and negative infinity passed to its finite-value guard.
- A zero critical center.
- A zero or negative rational denominator.
- A boolean masquerading as an integer numerator.

The exact coverage routine also returned the expected threshold 2650. These small controls test rejection contracts; they do not replace the full arithmetic replay. No verifier source was edited during this audit.

## Degree-extension proof: independent review passed

`docs/DEGREE_EXTENSION.md` uses $H=P/z-P'/N$. Since $N>n$, this is a nonconstant polynomial of degree $n-1$. The compact set $E=\{|H|\le L\}$ contains no zero of $P'$ when the original critical quotients exceed $L$. The uniform perturbation bound with $\delta=A/(B+1)$ keeps $(P+\epsilon z^N)'$ nonzero on $E$. At every critical point of the perturbed polynomial, its quotient equals $H(c)$, hence exceeds $L$.

This covers repeated critical points and all complex perturbations in the stated punctured disk. Exact degree and normalization hold. The empty-set case is handled. No continuity of individual critical roots is needed. The five exact integer endpoint comparisons and their overlap were independently checked.

The all-degrees theorem is conditional on the five exhaustive numerical certificates passing; it is existential for intermediate degrees. It does not provide an explicit perturbation coefficient for every such degree.

## Replay and trust scope

The release maintainer completed a fresh full five-witness arithmetic replay into `verification/release`: all 13,925 critical quotients passed. This auditor did not duplicate that run. The reports retain every interval and the exact input hashes. The preceding checks distinguish static reasoning, finite exported-bound aggregation, small rejection controls, and full recomputation.

The repository depends on the correctness of Python, python-flint/Arb and the checked verification code. A future theorem-prover formalization would require a proved arithmetic bridge, not importing the Arb output as an axiom. No completed Lean verification is asserted here.

## Reviewed file hashes

- `scripts/verify.py`: `5f65bf296b6b418bfdcf5a3154922cbc4758f7cbfca629f68b216d1245a2196e`.
- `docs/DEGREE_EXTENSION.md`: `41a34a5ea8fa06b15e1045709efc78bdec59f77158ecf7f0a4b5777962d14f66`.

The extension note’s links were localized after mathematical review; its proof and range arithmetic were unchanged. The hash above pins that localized version.
