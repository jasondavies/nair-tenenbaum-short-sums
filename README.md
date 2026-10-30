# Short sums of certain arithmetic functions

A Lean 4 / Mathlib formalisation of

> M. Nair and G. Tenenbaum, *Short sums of certain arithmetic functions*,
> Acta Mathematica **180** (1998), 119–144.

[Author's PDF](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf) ·
[DOI](https://doi.org/10.1007/BF02392880)

Registered with Palomar as
[PALOMAR-2026-10-30-000010, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000010&version=1),
verified at commit `9c3c923`.

**Theorems 1–3, Corollaries 1–10, and Lemma 2 have Lean proofs**, with the
corrections and scope conventions listed below. The printed Lemma 1 has a checked
counterexample; the comparisons needed by the main results are proved separately.
Corollary 6 requires a nonconstant restricted polynomial.

The [statement map](#paper-statements) links every numbered result to its proof.
The `*_for_families` declarations construct factorisation data from the original
integer polynomials. For proof dependencies and explanations of the source
corrections, see [BLUEPRINT.md](BLUEPRINT.md) and the
[completion audit](docs/completion-audit.yaml).

## Paper statements

Every numbered theorem, corollary, and lemma is accounted for here. All declaration
names have namespace `NairTenenbaum`.

| Paper statement | Declaration | Scope or correction |
| --- | --- | --- |
| Theorem 1 | [`theoremOne`](NairTenenbaum/Results/TheoremOne.lean), [`theoremOne_for_families`](NairTenenbaum/Results/FamilyTheorems.lean) | Original uniformity and height threshold |
| Theorem 2 | [`theoremTwo`](NairTenenbaum/Results/TheoremTwo.lean) | Every nonconstant irreducible integer polynomial; fixed prime divisors allowed |
| Theorem 3 | [`theoremThree`](NairTenenbaum/Results/TheoremThree.lean), [`theoremThree_for_families`](NairTenenbaum/Results/PrimeFamilyTheorem.lean) | Prime-argument estimate with the original growth exponent |
| Corollary 1 | [`corollaryOne`](NairTenenbaum/Results/CorollaryOne.lean), [`corollaryOne_for_families`](NairTenenbaum/Results/FamilyTheorems.lean) | Arithmetic progressions, with uniform constants |
| Corollary 2 | [`corollaryTwo`](NairTenenbaum/Results/CorollaryTwo.lean) | Irreducible pairwise coprime original polynomials |
| Corollary 3 | [`corollaryThree`](NairTenenbaum/Results/CorollaryThree.lean), [`corollaryThree_for_families`](NairTenenbaum/Results/FamilyTheorems.lean) | Products of scalar arithmetic functions |
| Corollary 4 | [`corollaryFour`](NairTenenbaum/Results/CorollaryFour.lean) | All real moment orders at least one |
| Corollary 5 | [`corollaryFive`](NairTenenbaum/Results/CorollaryFive.lean) | Uniform dyadic divisor average |
| Corollary 6 | [`corollarySix`](NairTenenbaum/Results/CorollarySix.lean), [`corollarySix_for_families`](NairTenenbaum/Results/SmoothFamilyTheorem.lean) | Requires a nonconstant restricted coordinate; [counterexample](NairTenenbaum/Counterexamples/CorollarySixObstruction.lean) otherwise |
| Corollary 7 | [`corollarySeven`](NairTenenbaum/Results/CorollarySeven.lean) | Corrects the transposed interval inequality to `x^(4ε) ≤ y ≤ x`, as inherited from Theorem 3 |
| Corollary 8 | [`corollaryEight`](NairTenenbaum/Results/CorollaryEight.lean) | Uniform for `1 ≤ \|a\| ≤ x` |
| Corollary 9 | [`corollaryNine`](NairTenenbaum/Results/CorollaryNine.lean) | Makes explicit the inherited range `1 ≤ \|a\| ≤ x`; eventually covers each fixed nonzero residue |
| Corollary 10 | [`corollaryTen`](NairTenenbaum/Results/CorollaryTen.lean) | Uniform short-interval Goldbach upper bound |
| Lemma 1 | [`LemmaOneObstruction.linearSystem_comparison_fails`](NairTenenbaum/Counterexamples/LemmaOneCounterexample.lean) | Printed comparison refuted; required [totient](NairTenenbaum/Arithmetic/ComparisonUniformity.lean) and [selected-prime](NairTenenbaum/Smooth/SelectedTiltComparison.lean) replacements proved |
| Lemma 2 | [`lemmaTwo`](NairTenenbaum/Results/LemmaTwo.lean) | General class-`M` weights, original cutoff, convergence, and uniform constant |

## Conventions and scope

Numbers in parentheses refer to equations in the paper.

* Arithmetic functions have domain `Fin k → ℕ+`. The coprimality hypothesis in
  (1) is coordinatewise; replacing it by coprimality of the total products would
  weaken the statement.
* The minimal majorant is the supremum of the ratios in (11), with zero adjoined.
  No attainment of the paper's written `max` is assumed. This also defines the
  majorant of the zero function correctly.
* In (16), coordinates are pairwise coprime **and each is coprime to `|D*|`**.
  `mem_weightFiber` proves that the finite bounding box loses no tuples when every
  total exponent is positive.
* `PolynomialSystem` records factors irreducible and pairwise nonassociated over
  `ℚ`, with unit signs retained. `FamilyFactorization` constructs these data for
  every original family with no fixed prime divisor, including constant unit
  polynomials. `FamilyTheorems` exposes the resulting estimates directly for
  those original polynomials. The `Q(X)=X` instance is also constructed explicitly.
* Polynomial evaluation uses the zero extension of an arithmetic function if any
  polynomial value vanishes. This is an explicit domain convention for terms
  otherwise undefined in the positive-integer formulation. `ShortSumDecomposition`
  proves that these terms vanish and includes them in the final estimate.
* The proved `TheoremOne` proposition has a threshold `c₀` independent of the
  coefficients and discriminant, and a bound constant `C(D)` depending on the
  specified bad-discriminant factor. Neither constant can depend on `F` or `x,y`.

## Palomar interface

[Challenge.lean](Challenge.lean) declares the 14 submission statements using only
Mathlib. Its `sorry` placeholders are deliberate; there are no definition holes.
[Solution.lean](Solution.lean) proves wrappers in `NairTenenbaum.Submission` from
the library theorems, without importing Challenge. The definitions repeated in
these two modules are intentional: their compiled types and transitive statement
constants must agree exactly.

[comparator.json](comparator.json) lists the claims and permitted axioms.
`scripts/verify-comparator.sh` uses the Comparator, NanoDa, and con-ron bundled
with the pinned Lean toolchain. It adds the external kernel configuration to a
temporary file, leaving the submitted configuration unchanged.

[formalization.yaml](formalization.yaml) records the v0.4 submission metadata,
including authorship, sources, review status, and source corrections.

## Build and verification

The project pins Lean **4.35.0** and Mathlib `v4.35.0`
(commit `56a005855ea17e0b0958f73ec801ae140b0a1679`). From the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

The check script builds the library, audits every library and Solution declaration
(including private and generated declarations), compares the submission statements,
and runs the `unusedArguments` linter. The library also enables Mathlib's standard
linter set. The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. No library or Solution proof uses `sorry`; the 14 intentional
placeholders are confined to Challenge.

For the submission checks and independent kernel verification, also run:

```sh
python3 scripts/check-submission.py  # requires PyYAML
bash scripts/verify-comparator.sh   # Linux only; requires Bubblewrap and permitted user/network namespaces
```

The recorded verification on 2026-10-30 audited **3,039 declarations**, with no
build warnings outside Challenge and no unused-argument lint errors.
`CheckStatements.lean` found exact agreement of all **14 theorem types** and
**19,610 transitive statement constants**. Comparator exported the proofs, and
**con-ron, NanoDa, and Lean's default kernel** accepted the solution.
[CI](.github/workflows/ci.yml) runs these checks and validates the submission
metadata against its schema.

## Library layout

Individual module imports use the subject folders under
[NairTenenbaum](NairTenenbaum), while `import NairTenenbaum` loads the complete
library. The [module index](docs/modules.md) describes every module, and the
[blueprint](BLUEPRINT.md) presents most of them in proof order.

| Folders | Contents |
| --- | --- |
| `Arithmetic`, `Polynomials` | Arithmetic weights, prime factors, root counts, and polynomial systems |
| `Sieve`, `Smooth`, `Contributions` | Shared sieve, moment, splitting, and interval arguments |
| `PrimeArguments`, `Progressions` | Prime arguments and arithmetic progression specialisations |
| `Hooley`, `DivisorSums` | Hooley moments, divisor hits, and greatest-prime-factor estimates |
| `NumberFields`, `Geometry` | Ideal counting and the lattice estimates supporting root density |
| `Results`, `Counterexamples` | Numbered results, family interfaces, and source obstructions |

## Licence

The [Apache-2.0 licence](LICENSE) applies to this repository, not to the cited papers.
