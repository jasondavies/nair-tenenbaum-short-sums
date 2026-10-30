# Short sums of certain arithmetic functions

A Lean 4 / Mathlib formalization of

> M. Nair and G. Tenenbaum, *Short sums of certain arithmetic functions*,
> Acta Mathematica **180** (1998), 119–144.

[Author's PDF](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf) ·
[DOI](https://doi.org/10.1007/BF02392880)

**Theorems 1–3, Corollaries 1–10, and Lemma 2 have Lean proofs**, with the
explicit corrections and scope conventions listed below. Corollary 6 requires
a nonconstant restricted polynomial. The printed Lemma 1 has a checked
counterexample; the comparisons needed by the main results are proved separately.
[`theoremOne`](NairTenenbaum/Results/TheoremOne.lean) proves the recorded proposition
`TheoremOne`, including the coefficient-independent height threshold and the
restricted-discriminant dependence of the bound.
[FamilyTheorems](NairTenenbaum/Results/FamilyTheorems.lean) exports Theorem 1 and
Corollaries 1 and 3 directly for the original integer polynomials, with all
factorization data constructed from the no-fixed-prime hypothesis.
[`corollaryOne`](NairTenenbaum/Results/CorollaryOne.lean) proves the arithmetic-progression
estimate, including a height threshold independent of the progression parameter
`β` and a bound depending on the original restricted discriminant.
[`corollaryTwo`](NairTenenbaum/Results/CorollaryTwo.lean) proves the explicit tuple bound
for irreducible pairwise coprime polynomials, constructing its factorization
data from the original integer polynomials.
[`corollaryThree`](NairTenenbaum/Results/CorollaryThree.lean) proves the factored bound
for products of arithmetic functions on pairwise coprime polynomials.
[`theoremThree`](NairTenenbaum/Results/TheoremThree.lean) proves the prime-argument
estimate with its height threshold, logarithmic saving, and explicit
constant-term correction. The proof handles the small fixed primes that
adjoining `X` can introduce, while retaining the original degree in the
arithmetic-function growth condition.
[PrimeFamilyTheorem](NairTenenbaum/Results/PrimeFamilyTheorem.lean) exports the bound
for original polynomial families with factorization data constructed.
[`corollarySeven`](NairTenenbaum/Results/CorollarySeven.lean) specializes it to shifted
primes, with constants independent of the nonzero integer shift.
[`corollaryTen`](NairTenenbaum/Results/CorollaryTen.lean) proves the Goldbach bound with
one prime in a short interval, including constants uniform in the represented integer.
[`corollarySix`](NairTenenbaum/Results/CorollarySix.lean) proves the smoothness-restricted
estimate when the restricted polynomial is nonconstant.
[SmoothFamilyTheorem](NairTenenbaum/Results/SmoothFamilyTheorem.lean) exports it for the
original polynomial families. The proof includes the uniform weighted comparison
(41) and handles small polynomial values separately, retaining the original
height and interval hypotheses.
The nonconstancy condition is necessary if constant unit coordinates are allowed:
[CorollarySixObstruction](NairTenenbaum/Counterexamples/CorollarySixObstruction.lean) proves that
`Q₁=X`, `Q₂=1`, `F=1` defeats every proposed uniform bound.
[`theoremTwo`](NairTenenbaum/Results/TheoremTwo.lean) proves the greatest-prime-factor
bound for every nonconstant irreducible integer polynomial, every fixed integer
`k > degree`, and every `α < 2 - log 4`, including polynomials with fixed prime
divisors. The proof combines the unconditional divisor-hit estimate with a
quantitative rough logarithmic-mass bound. The latter uses the sharp weighted
prime-root estimate `Σ ρ_Q(p) log(p)/p ≤ log(x)+O_Q(1)`, proved from a power-saving
ideal count. Finite smooth boundary charts of the number-field fundamental
region supply the lattice discrepancy; summing over ideal classes gives
`A_K(x)=κ_K*x+O(x^((degree-1)/degree))`. The leading coefficient is identified
with the positive Dedekind zeta residue. The error is then absorbed by the
divisor-hit saving, giving the strict exponential gain in Theorem 2.
Corollary 4 is now proved, including the
irreducible-polynomial sieve-product bound `≪1/log(x)`.
Their Hooley short-sum specializations and the exact divisor-sum rearrangements
for Corollaries 5 and 9 are proved. The shifted-prime specialization covers
`1 ≤ |a| ≤ x` uniformly. [HooleyAverageReductions](NairTenenbaum/Hooley/HooleyAverageReductions.lean)
reduces both dyadic averages to the reciprocal Hooley mean. The sharp estimate
for that mean and Corollaries 5, 8, and 9 are now proved. The reciprocal-totient
factor is absorbed uniformly for `1≤|a|≤x`; Corollary 9 uses this inherited
residue range and holds eventually for every fixed nonzero residue.
The integral-moment comparison, prime recurrence, mixed-term estimate, and
fractional-power prime step are proved. The squarefree moment Dirichlet series
now has proved convergence, a termwise derivative, and an exact prime expansion
for every real argument greater than one. The infinite prime step and Hölder
interpolation give the nonlinear differential inequality. Its divisor Euler
bound, exact integrating factor, integrated endpoint estimate, and elementary
prime-series pole bound are proved. The sharp bound
`Σ_p ρ_Q(p)/p^σ ≤ −log(σ−1)+O_Q(1)` is now proved for every integer
polynomial irreducible over ℚ, using the Dedekind zeta residue and a proved
integral-normalization reduction. The explicit power majorant, its integral,
and a quantitative exponent gap are also proved. Recovering the original
series gives a bound uniform in the moment order. The integer optimization
and sharp reciprocal mean over all positive integers are now proved, with
exponential coefficient `sqrt(2t)+o(1)`. The passage from squarefree integers
uses a coprime decomposition and a convergent divisor-weighted sum over powerful integers.
A verified counterexample to the printed Lemma 1 is recorded in
[LemmaOneCounterexample](NairTenenbaum/Counterexamples/LemmaOneCounterexample.lean). Its hypothesis
(23) does not imply its comparison (24), even for `Q=X` and arbitrarily small
positive growth exponents. A corrected comparison for the totient twist used in
the main proof is proved, including the full multivariable weight and uniform constants.
[`lemmaTwo`](NairTenenbaum/Results/LemmaTwo.lean) proves the general class-`M` version of
Lemma 2, including convergence, the original cutoff `x > z > 4^(γκ)`, and a
constant independent of `F`, `D`, `x`, and `z` for fixed growth data and scalar
weights. The proof uses prime-factor roots to absorb arbitrary, potentially
nonmultiplicative weights into additional arithmetic coordinates. Squaring the
weighted mass and halving the decay parameter preserve the required cutoff.
The root-vector and totient-modified specializations also have constants uniform
in degree and restricted discriminant.
The counterexample does not by itself refute
the main theorems. See [the proof map](BLUEPRINT.md).

## Paper statements

Every numbered theorem, corollary, and lemma is accounted for here. All declaration
names have namespace `NairTenenbaum`.

| Paper statement | Declaration | Scope or correction |
| --- | --- | --- |
| Theorem 1 | [`theoremOne`](NairTenenbaum/Results/TheoremOne.lean), [`theoremOne_for_families`](NairTenenbaum/Results/FamilyTheorems.lean) | Original uniformity and height threshold |
| Theorem 2 | [`theoremTwo`](NairTenenbaum/Results/TheoremTwo.lean) | Every nonconstant irreducible integer polynomial; fixed prime divisors allowed |
| Theorem 3 | [`theoremThree`](NairTenenbaum/Results/TheoremThree.lean), [`theoremThree_for_families`](NairTenenbaum/Results/PrimeFamilyTheorem.lean) | Prime-argument estimate with the original growth exponent |
| Corollary 1 | [`corollaryOne`](NairTenenbaum/Results/CorollaryOne.lean) | Arithmetic progressions, with uniform constants |
| Corollary 2 | [`corollaryTwo`](NairTenenbaum/Results/CorollaryTwo.lean) | Irreducible pairwise coprime original polynomials |
| Corollary 3 | [`corollaryThree`](NairTenenbaum/Results/CorollaryThree.lean) | Products of scalar arithmetic functions |
| Corollary 4 | [`corollaryFour`](NairTenenbaum/Results/CorollaryFour.lean) | All real moment orders at least one |
| Corollary 5 | [`corollaryFive`](NairTenenbaum/Results/CorollaryFive.lean) | Uniform dyadic divisor average |
| Corollary 6 | [`corollarySix`](NairTenenbaum/Results/CorollarySix.lean) | Requires a nonconstant restricted coordinate; [counterexample](NairTenenbaum/Counterexamples/CorollarySixObstruction.lean) otherwise |
| Corollary 7 | [`corollarySeven`](NairTenenbaum/Results/CorollarySeven.lean) | Corrects the transposed interval inequality to `x^(4ε) ≤ y ≤ x` |
| Corollary 8 | [`corollaryEight`](NairTenenbaum/Results/CorollaryEight.lean) | Uniform for `1 ≤ |a| ≤ x` |
| Corollary 9 | [`corollaryNine`](NairTenenbaum/Results/CorollaryNine.lean) | Makes explicit the inherited range `1 ≤ |a| ≤ x`; eventually covers each fixed nonzero residue |
| Corollary 10 | [`corollaryTen`](NairTenenbaum/Results/CorollaryTen.lean) | Uniform short-interval Goldbach upper bound |
| Lemma 1 | [`LemmaOneObstruction.linearSystem_comparison_fails`](NairTenenbaum/Counterexamples/LemmaOneCounterexample.lean) | Printed comparison refuted; required [totient](NairTenenbaum/Arithmetic/ComparisonUniformity.lean) and [selected-prime](NairTenenbaum/Smooth/SelectedTiltComparison.lean) replacements proved |
| Lemma 2 | [`lemmaTwo`](NairTenenbaum/Results/LemmaTwo.lean) | General class-`M` weights, original cutoff, convergence, and uniform constant |

## Palomar submission preparation

[Challenge.lean](Challenge.lean) is the independent, Mathlib-only statement surface:
Theorems 1–3, Corollaries 1–10, and Lemma 2, with the scope corrections above.
Its definitions agree definitionally with the library definitions; its fourteen
`sorry` placeholders are intentional theorem statements, and there are no definition holes.
[Solution.lean](Solution.lean) proves wrappers in `NairTenenbaum.Submission`
directly from the library theorems by definitional equality, without importing
Challenge. Keeping the submission definitions together makes their generated
helper names agree across the two modules. [comparator.json](comparator.json) names all fourteen
claims and permits only `propext`, `Classical.choice`, and `Quot.sound`.

[formalization.yaml](formalization.yaml) uses the upstream v0.4 format and records
Jason Davies as author and maintainer, Apache-2.0 licensing, mathematical sources,
classification, automation, review status, and source divergences. The earlier
full progress inventory is preserved in [docs/completion-audit.yaml](docs/completion-audit.yaml).
The [LICENSE](LICENSE) applies to this repository, not to the cited papers.

Run these checks from the repository root:

```bash
python3 scripts/check-submission.py  # requires PyYAML
bash scripts/check.sh
bash scripts/verify-comparator.sh   # requires Bubblewrap and a host allowing user/network namespaces
```

The final command uses the Comparator bundled with the pinned Lean toolchain and
adds its bundled NanoDa and con-ron checkers to a temporary configuration. The
submitted `comparator.json` contains no `external_kernels` field, as required by
Palomar. [CI](.github/workflows/ci.yml) runs the layout checks, validates the
metadata against the upstream schema, builds both modules, audits the library
and submission theorems, checks their compiled statement definitions for exact
agreement, checks unused declaration arguments, and runs Comparator.

Preparation checks passed: both modules compile; the metadata validates against
the upstream v0.4 schema; the source-layout and axiom audits pass.
`scripts/CheckStatements.lean` also confirms exact agreement of all fourteen
compiled theorem types and 19,610 transitive statement constants; this local
comparison does not export or independently recheck the proofs. The Challenge
is 469 lines and 22,705 bytes, below the 1,000-line and 100 KiB hard limits.
The refactored working tree passed `scripts/verify-comparator.sh` on 2026-10-30:
sandboxed Comparator exported the proofs, and con-ron, NanoDa, and Lean's default
kernel all accepted the solution. The run used host permissions for Bubblewrap's
namespace sandbox. No Palomar registration is claimed.

Commit and push the complete snapshot, including
`lake-manifest.json`, to a public GitHub repository. Use its full 40-character
commit SHA for the [Palomar submission](https://palomar-registry.org/how-to-submit).
The project is at the repository root and uses the conventional paths
`comparator.json` and `formalization.yaml`, so the optional path fields can remain
blank. No public repository URL or submission SHA has been supplied or verified
in this workspace, and no submission has been sent.

## Library layout

The public namespace remains `NairTenenbaum`. Individual module imports use the
subject folders under [NairTenenbaum](NairTenenbaum), while
`import NairTenenbaum` loads the complete library.

| Folders | Contents |
| --- | --- |
| `Arithmetic`, `Polynomials` | Arithmetic weights, prime factors, root counts, and polynomial systems |
| `Sieve`, `Smooth`, `Contributions` | Shared sieve, moment, splitting, and interval arguments |
| `PrimeArguments`, `Progressions` | Prime arguments and arithmetic progression specializations |
| `Hooley`, `DivisorSums` | Hooley moments, divisor hits, and greatest-prime-factor estimates |
| `NumberFields`, `Geometry` | Ideal counting and the lattice estimates supporting root density |
| `Results`, `Counterexamples` | Numbered results, family interfaces, and source obstructions |

## Build and audit

The toolchain is Lean **4.35.0**, with Mathlib pinned to `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
bash scripts/check.sh
```

The library enables Mathlib’s standard linter set. The check script also runs
the `unusedArguments` declaration linter and audits every declaration defined by its
modules, including private and generated declarations. The only permitted axioms
are `propext`, `Classical.choice`, and `Quot.sound`. A source module missing from
the audit's explicit `import all` list is an error. No library or Solution proof uses `sorry` or an additional axiom.
Challenge contains only the deliberate statement placeholders described above. The completed audit checks **3,060 declarations**.
The statement map above and [completion audit](docs/completion-audit.yaml) record
which printed statements are proved, corrected, or refuted. The additional
submission audit checks every theorem listed in `comparator.json` and confirms
that `Solution` does not import `Challenge`.

During initial development the already-cached dependency packages from
`../iwaniec-linear-sieve` were copied into this project's ignored `.lake` directory.
The tracked Lake configuration uses pinned Git dependencies, with no sibling
project or absolute-path dependencies.

## Implemented material

All names below are in the `NairTenenbaum` namespace.

| Module | Content |
|---|---|
| [FloorRootArithmetic](NairTenenbaum/Arithmetic/FloorRootArithmetic.lean) | Coprime multiplicativity of prime-factor roots and preservation of scalar admissibility |
| [AppendArithmetic](NairTenenbaum/Arithmetic/AppendArithmetic.lean) | Products on independent coordinate blocks; scalar class `M` and common constants |
| [LiftedWeights](NairTenenbaum/Smooth/LiftedWeights.lean) | Doubled exponent matrix, squared mass, and exact encoding of scalar weights |
| [LiftedWeightSums](NairTenenbaum/Smooth/LiftedWeightSums.lean) | Smooth-tail and truncated-sum comparisons under the lift |
| [GeneralSmoothTail](NairTenenbaum/Smooth/GeneralSmoothTail.lean) | Finite and convergent infinite tails for general admissible scalar weights |
| [LemmaTwo](NairTenenbaum/Results/LemmaTwo.lean) | Full Lemma 2 with class-`M` weights and Theorem 1 parameters, including cutoffs below two |
| [Arithmetic](NairTenenbaum/Arithmetic/Arithmetic.lean) | Positive tuples; `Ω`; equation (1); parameter monotonicity; addition, scaling and real powers; vanishing when `F(1)=0` |
| [MinimalMajorant](NairTenenbaum/Arithmetic/MinimalMajorant.lean) | Equation (11) as a supremum; equations (12)–(13); minimality, submultiplicativity, and admissibility of `G_F` |
| [PrimeMajorant](NairTenenbaum/Arithmetic/PrimeMajorant.lean) | Prime-part decomposition of tuples and the full multivariable bound (14) |
| [AuxiliaryFunctions](NairTenenbaum/Arithmetic/AuxiliaryFunctions.lean) | The multiplicative functions `f_h`, local geometric bounds, and the arbitrary-tuple bound (17) |
| [AuxiliarySeries](NairTenenbaum/Arithmetic/AuxiliarySeries.lean) | Convergence and tails of the local series; the finite Euler product over smooth integers |
| [PrimeSplitting](NairTenenbaum/Arithmetic/PrimeSplitting.lean) | Full prime-part selection, cross-coordinate coprimality, exact factorizations, and (29)–(30) |
| [RootCount](NairTenenbaum/Polynomials/RootCount.lean) | Equation (10); CRT multiplicativity; prime root bound by degree; invariance under removing positive powers at primes; linear examples; positivity of the sieve product |
| [PrimePowerRoots](NairTenenbaum/Arithmetic/PrimePowerRoots.lean) | Root reduction; vanishing at multiples of a root-free modulus; injectivity on simple roots; exponent-independent root bounds under separable reduction |
| [DiscriminantBezout](NairTenenbaum/Polynomials/DiscriminantBezout.lean) | Bézout identity for the discriminant in degree at least two; simple residue roots away from the discriminant, including primes dividing the leading coefficient |
| [BadPrimeRoots](NairTenenbaum/Sieve/BadPrimeRoots.lean) | Root clustering via Taylor expansion; `ρ_Q(p^ν) ≤ p^(2 v_p(discr Q)+1)` in degree at least two |
| [CongruenceCount](NairTenenbaum/Arithmetic/CongruenceCount.lean) | Counts in integer intervals: the error from `(b-a)ρ_Q(q)/q` is at most `ρ_Q(q)`, for every positive modulus |
| [Weights](NairTenenbaum/Arithmetic/Weights.lean) | Exponent substitution, equations (15)–(16), both dagger restrictions, finiteness of fibers, and exact one-variable specialization |
| [PolynomialSystem](NairTenenbaum/Polynomials/PolynomialSystem.lean) | Equation (9), factorization data, discriminants, coefficient height, root vectors, short sums and the main term |
| [PolynomialStructure](NairTenenbaum/Polynomials/PolynomialStructure.lean) | Degree identities, bounds on the number of factors, rational separability, and nonzero discriminant of the radical |
| [PolynomialHeight](NairTenenbaum/Polynomials/PolynomialHeight.lean) | Coefficient and value bounds in terms of the polynomial height and degree |
| [PolynomialLocal](NairTenenbaum/Polynomials/PolynomialLocal.lean) | Prime-power root bounds at all primes, uniformly by `max(deg R_h,D³)`; common value-divisors of distinct factors divide `D*` |
| [PrimeLogSums](NairTenenbaum/Arithmetic/PrimeLogSums.lean) | Elementary logarithmic prime sums and cutoff-uniform bounds for `p^(κ/log z)-1` |
| [TiltedAuxiliary](NairTenenbaum/Smooth/TiltedAuxiliary.lean) | Convergence and finite smooth Euler products after exponential tilting; exact local moment increments |
| [MomentPrimeBounds](NairTenenbaum/Smooth/MomentPrimeBounds.lean) | A cutoff-uniform bound for root-weighted moment-correction Euler products, with the exponent gap and root bounds discharged |
| [PrimePowerComparison](NairTenenbaum/Arithmetic/PrimePowerComparison.lean) | Valuation-dependent prime increments and finite convolution with separate coordinate domains |
| [MomentKernel](NairTenenbaum/Smooth/MomentKernel.lean) | Convergent Euler product for the exponential-moment kernel and bounds for its smooth partial sums |
| [SmoothMoment](NairTenenbaum/Smooth/SmoothMoment.lean) | Global finite moments and Rankin tails for smooth dagger tuples, uniform in both cutoffs |
| [SmoothWeightSum](NairTenenbaum/Smooth/SmoothWeightSum.lean) | Exact reindexing into the paper's weight notation and the root-weighted smooth tail bound for polynomial systems |
| [PrimeBandBounds](NairTenenbaum/Smooth/PrimeBandBounds.lean) | Reciprocal prime sums and uniform root-auxiliary Euler products on a band of primes |
| [SmoothCutoffComparison](NairTenenbaum/Smooth/SmoothCutoffComparison.lean) | Comparison of two smoothness cutoffs with the dagger restrictions and mass bound preserved |
| [SmoothTruncation](NairTenenbaum/Smooth/SmoothTruncation.lean) | Explicit smaller cutoff and absorption of its smooth tail |
| [SmoothTruncationUniform](NairTenenbaum/Smooth/SmoothTruncationUniform.lean) | Reduction of full finite smooth sums to mass at most `z`, for every `z≥2` |
| [RootSmoothTail](NairTenenbaum/Smooth/RootSmoothTail.lean) | Convergent infinite root-weighted smooth tail with the exponential saving and a right-hand sum truncated at `z` |
| [TiltedTotientComparison](NairTenenbaum/Smooth/TiltedTotientComparison.lean) | Corrected totient comparison after exponential tilting, uniform below a fixed convergence exponent |
| [TotientSmoothTail](NairTenenbaum/Smooth/TotientSmoothTail.lean) | Convergent totient-modified smooth tails bounded by the truncated original root weight |
| [SmoothTailUniformity](NairTenenbaum/Smooth/SmoothTailUniformity.lean) | Positive smooth-tail constants depending only on growth parameters, degree and restricted discriminant; Theorem 1 parameter specialization |
| [DiscriminantSplitting](NairTenenbaum/Polynomials/DiscriminantSplitting.lean) | Full discriminant-prime removal gives dagger tuples and a cross-coprime factorization; removed support lies in the restricted bad discriminant |
| [FractionalAuxiliary](NairTenenbaum/Arithmetic/FractionalAuxiliary.lean) | Convergent auxiliary series with fractional denominators and uniform finite smooth bounds |
| [BadPrimeMass](NairTenenbaum/Sieve/BadPrimeMass.lean) | Least-common-multiple density and convergence of the full bad-prime tuple series, uniformly in degree and restricted discriminant |
| [PrimeFactorBounds](NairTenenbaum/Arithmetic/PrimeFactorBounds.lean) | Uniform subpolynomial bounds for `K^ω(n)` and least-common-multiple majorants |
| [SelbergDenominator](NairTenenbaum/Sieve/SelbergDenominator.lean) | Exact logarithmic moment and quantitative denominator bound: at least one quarter of the full Euler product at cutoff `z^(2g)` when `log z≥16` |
| [SelbergCoefficientBounds](NairTenenbaum/Sieve/SelbergCoefficientBounds.lean) | Uniform local and subpolynomial bounds for the optimized sieve coefficients |
| [SelbergRemainder](NairTenenbaum/Sieve/SelbergRemainder.lean) | Quadratic remainder estimate and quantitative sieve upper bound with a constant depending only on dimension and the error exponent |
| [OmittedEulerFactors](NairTenenbaum/Sieve/OmittedEulerFactors.lean) | Missing Euler factors bounded by `(n/φ(n))^g` times an explicit degree-only constant |
| [SievePrimes](NairTenenbaum/Sieve/SievePrimes.lean) | Actual sieve prime product, omission of root-free and modulus primes, and restoration of the full sifting product |
| [SieveProductLowerBound](NairTenenbaum/Sieve/SieveProductLowerBound.lean) | Uniform bound `sieveProduct(Q,z)⁻¹ ≪ z^δ` for every positive exponent |
| [SieveLevel](NairTenenbaum/Sieve/SieveLevel.lean) | Conditional sieve remainder absorbed under an explicit modulus-and-cutoff size condition |
| [TotientProducts](NairTenenbaum/Arithmetic/TotientProducts.lean) | Totient corrections for arbitrary products and prime-support inclusions |
| [BadPrimeSieve](NairTenenbaum/Sieve/BadPrimeSieve.lean) | Conditional sieve with bad-part LCM density and uniform summation over every bad-prime valuation |
| [SmallDivisorSieve](NairTenenbaum/Sieve/SmallDivisorSieve.lean) | Summation over good tuples and removal of their totient correction |
| [SiftedDivisorSplit](NairTenenbaum/Sieve/SiftedDivisorSplit.lean) | Shared divisor splitting and fiber-counting proofs for integer and prime arguments |
| [SmallDivisorSum](NairTenenbaum/Sieve/SmallDivisorSum.lean) | Reindexing from the original divisor tuples and a single weighted-mass sieve level |
| [SieveScales](NairTenenbaum/Sieve/SieveScales.lean) | The paper’s small-divisor scales satisfy the sieve level uniformly in the polynomial coefficients |
| [SieveCutoffComparison](NairTenenbaum/Sieve/SieveCutoffComparison.lean) | Uniform comparison of the sifting products at a power cutoff and the original cutoff |
| [SmallDivisorMainTerm](NairTenenbaum/Sieve/SmallDivisorMainTerm.lean) | The sifted small-divisor sum bounded by the original main term, with uniform constants |
| [RoughMass](NairTenenbaum/Arithmetic/RoughMass.lean) | Prime-factor count and arithmetic-growth bounds for rough remaining factors |
| [PolynomialValueTuples](NairTenenbaum/Polynomials/PolynomialValueTuples.lean) | Positive value tuples, exact weighted total value, and the sieve condition for selected prefixes |
| [PolynomialValueBounds](NairTenenbaum/Polynomials/PolynomialValueBounds.lean) | Uniform power bound for polynomial values under the height hypothesis |
| [SmallDivisorMajorant](NairTenenbaum/Sieve/SmallDivisorMajorant.lean) | Grouping selected prefixes by divisor tuple proves the first-contribution sieve majorant |
| [FirstContribution](NairTenenbaum/Contributions/FirstContribution.lean) | The small rough-prefix class and its reduction to the sifted divisor sum |
| [RealIntervalBounds](NairTenenbaum/Contributions/RealIntervalBounds.lean) | Integer endpoint bounds and exact natural-to-integer interval reindexing |
| [FirstContributionReal](NairTenenbaum/Contributions/FirstContributionReal.lean) | Real and positive integral cutoffs for the small rough-prefix predicate |
| [PrimePowerThreshold](NairTenenbaum/Arithmetic/PrimePowerThreshold.lean) | Least prime power above a threshold and large coordinate prime powers forced by a prefix crossing |
| [PrimePowerCounting](NairTenenbaum/Arithmetic/PrimePowerCounting.lean) | Elementary union bound for large powers of small primes, with density at most a constant times z/T |
| [SecondContributionCounting](NairTenenbaum/Contributions/SecondContributionCounting.lean) | Second-class inclusion in the exceptional set and degree/discriminant-uniform counting |
| [ValueWeightBounds](NairTenenbaum/Arithmetic/ValueWeightBounds.lean) | Pointwise arithmetic-weight bounds retaining the degree-only coefficient |
| [MainTermLowerBound](NairTenenbaum/Arithmetic/MainTermLowerBound.lean) | Unit weight and uniform absorption of power-saving errors into the original main term |
| [SecondContributionWeights](NairTenenbaum/Contributions/SecondContributionWeights.lean) | Weighted exceptional-set estimate with the saving x^(-ε/3) |
| [SecondContribution](NairTenenbaum/Contributions/SecondContribution.lean) | Small-crossing-prime predicate, scale identity, and sieve-level bound |
| [SmoothDivisorDensity](NairTenenbaum/Smooth/SmoothDivisorDensity.lean) | Reciprocal-density tail for smooth moduli and uniform radical root counts at every prime power |
| [SmoothDivisorCounting](NairTenenbaum/Smooth/SmoothDivisorCounting.lean) | Large smooth divisor tuples mapped to one radical-value divisor through their least common multiple |
| [ThirdContributionWeights](NairTenenbaum/Contributions/ThirdContributionWeights.lean) | Weighted bounded-smoothness estimate with the saving x^(-ε/12) |
| [ThirdContribution](NairTenenbaum/Contributions/ThirdContribution.lean) | Large smooth-divisor predicate and sieve-level bound |
| [BadPrimeMoments](NairTenenbaum/Sieve/BadPrimeMoments.lean) | Uniform positive moments of the full bad-prime tuple kernel, including every valuation |
| [SmoothMomentUniformity](NairTenenbaum/Smooth/SmoothMomentUniformity.lean) | Totient-modified smooth moments bounded by the original truncated weight sum with uniform constants |
| [SplitSmoothTail](NairTenenbaum/Smooth/SplitSmoothTail.lean) | Smooth-tail saving on the combined bad/good prefix mass |
| [SmoothTailSieveReindex](NairTenenbaum/Smooth/SmoothTailSieveReindex.lean) | Original smooth divisor tail reindexed without losing its mass cutoff |
| [SmoothTailSieve](NairTenenbaum/Smooth/SmoothTailSieve.lean) | Conditional sieve on a smooth mass tail with separate smoothness and sifting cutoffs |
| [LargePrefixScales](NairTenenbaum/Smooth/LargePrefixScales.lean) | Uniform sieve level for prefixes up to x^(3g²ε) and prime cutoffs at most x^(gε/16) |
| [SmoothTailMajorant](NairTenenbaum/Smooth/SmoothTailMajorant.lean) | Selected-prefix reduction retaining the original lower mass cutoff and smoothness support |
| [PrimeBandDecay](NairTenenbaum/Smooth/PrimeBandDecay.lean) | Tail decay after paying arithmetic and Euler-product costs; dyadic band cover and geometric summation |
| [PrimeBandMajorant](NairTenenbaum/Smooth/PrimeBandMajorant.lean) | One-band sifted estimate with constants independent of the band index |
| [PrimeBandContribution](NairTenenbaum/Smooth/PrimeBandContribution.lean) | One-band estimate for the original arithmetic weights |
| [PrimeBandSummation](NairTenenbaum/Smooth/PrimeBandSummation.lean) | Uniform bound for any finite collection of eligible logarithmic bands |
| [PrimeBandCutoff](NairTenenbaum/Smooth/PrimeBandCutoff.lean) | A fixed cutoff supplies every band condition; positive moment strength chosen before the polynomials |
| [PrimeBandCover](NairTenenbaum/Smooth/PrimeBandCover.lean) | Actual prefixes assigned to eligible bands, including the finite-interval cover |
| [IntermediateContribution](NairTenenbaum/Contributions/IntermediateContribution.lean) | Entire intermediate-prime contribution bounded using the polynomial height hypothesis |
| [IntermediateContributionReal](NairTenenbaum/Contributions/IntermediateContributionReal.lean) | Real and positive integral cutoffs for the intermediate-prefix predicate |
| [ConditionalPolynomialSieve](NairTenenbaum/Sieve/ConditionalPolynomialSieve.lean) | The global no-fixed-prime specialization of the local conditional sieve |
| [PolynomialSieve](NairTenenbaum/Polynomials/PolynomialSieve.lean) | Polynomial-value sieve in integer intervals, with coefficient-independent constants and the congruence remainder discharged |
| [SelbergWeights](NairTenenbaum/Sieve/SelbergWeights.lean) | Optimized truncated Selberg coefficients, exact reciprocal-denominator main term, and remainder support through the square of the cutoff |
| [JointCongruence](NairTenenbaum/Sieve/JointCongruence.lean) | Exact CRT density and interval error for simultaneous polynomial congruences; mixed bad-part and good-coordinate counting bounds |
| [BadPrimeCongruence](NairTenenbaum/Sieve/BadPrimeCongruence.lean) | Uniform summation of bad-prime congruence contributions, including admissible arithmetic weights |
| [PrimeThreshold](NairTenenbaum/Arithmetic/PrimeThreshold.lean) | First prime crossing a real weighted-mass threshold, equation (28), and the small-total-mass alternative |
| [RootAuxiliary](NairTenenbaum/Arithmetic/RootAuxiliary.lean) | Root-weighted multiplicative majorants, local convergence and finite Euler products, with the polynomial hypotheses discharged |
| [UnitaryComparison](NairTenenbaum/Arithmetic/UnitaryComparison.lean) | Finite scalar comparison by an injective split into complementary whole prime-power factors |
| [ComparisonKernel](NairTenenbaum/Arithmetic/ComparisonKernel.lean) | Kernel Euler products and a global scalar comparison with a constant independent of the cutoff |
| [ScalarComparison](NairTenenbaum/Arithmetic/ScalarComparison.lean) | Corrected scalar totient comparison for admissible functions and the actual polynomial factors, with an explicit uniform constant |
| [TupleComparison](NairTenenbaum/Arithmetic/TupleComparison.lean) | Multivariable whole prime-power splitting and the finite kernel comparison |
| [WeightTruncation](NairTenenbaum/Arithmetic/WeightTruncation.lean) | Dagger preservation, cross-coprimality, weighted-mass cutoffs, and exact reindexing of finite weight sums |
| [MultivariableComparison](NairTenenbaum/Arithmetic/MultivariableComparison.lean) | Corrected totient comparison for the full weight (16), all real cutoffs, and actual polynomial systems |
| [ComparisonUniformity](NairTenenbaum/Arithmetic/ComparisonUniformity.lean) | Comparison constant depending only on degree, growth parameters, and restricted discriminant |
| [ComparisonLocal](NairTenenbaum/Arithmetic/ComparisonLocal.lean) | Root-weighted tail bounds, a sufficient local comparison criterion, and bounded finite Euler products |
| [TotientTwist](NairTenenbaum/Arithmetic/TotientTwist.lean) | Reciprocal-totient correction; its stronger weighted local condition for the actual polynomial factors |
| [LemmaOneObstruction](NairTenenbaum/Counterexamples/LemmaOneObstruction.lean) | Failure of the local summability deduction used in Lemma 1 |
| [PrimeSupportedFunction](NairTenenbaum/Counterexamples/PrimeSupportedFunction.lean) | Admissible functions supported on powers of two and completely multiplicative twists |
| [LemmaOneCounterexample](NairTenenbaum/Counterexamples/LemmaOneCounterexample.lean) | Full arithmetic counterexample to the printed comparison in Lemma 1, including (23) and the weights for `Q=X` |
| [Hooley](NairTenenbaum/Hooley/Hooley.lean) | `Δ`, attainment of its maximum, coprime divisor-window identity, `Δ(mn) ≤ τ(m)Δ(n)`, and the pointwise dyadic divisor bound |
| [DivisorBounds](NairTenenbaum/Arithmetic/DivisorBounds.lean) | `τ(n) ≤ 2^Ω(n)`; `τ(n) ≪_ε n^ε`; admissibility of `Δ` and every positive real power of `Δ` |
| [Normalization](NairTenenbaum/Arithmetic/Normalization.lean) | Homogeneity of sums and weights; reduction of a short-sum estimate to `F(1)=1`, with the estimate explicitly assumed |
| [LinearCase](NairTenenbaum/Polynomials/LinearCase.lean) | An explicit `Q(X)=X` instance and the specialization of its weight and main term |
| [LargePrefixMainTerm](NairTenenbaum/Smooth/LargePrefixMainTerm.lean) | Sifted large-prefix sum bounded by the original main term |
| [ShortSumDecomposition](NairTenenbaum/Contributions/ShortSumDecomposition.lean) | Exhaustive four-majorant cover, including small total values and zero-extension terms |
| [Targets](NairTenenbaum/Results/Targets.lean) | Proposition `TheoremOne`, with uniform constants quantified before the polynomial family and function |
| [TheoremOne](NairTenenbaum/Results/TheoremOne.lean) | Proof `theoremOne : TheoremOne` and a bound uniform in the numbers of polynomials and factors at fixed degree |
| [AffineRootCounts](NairTenenbaum/Progressions/AffineRootCounts.lean) | Root counts and omitted-prime Euler product after arithmetic-progression substitution |
| [AffinePolynomialSystem](NairTenenbaum/Progressions/AffinePolynomialSystem.lean) | Construction of the substituted system, preserving irreducibility, nonassociation, and total degree |
| [AffineDiscriminant](NairTenenbaum/Progressions/AffineDiscriminant.lean) | Exact resultant and discriminant scaling under affine substitution |
| [AffineBadDiscriminant](NairTenenbaum/Progressions/AffineBadDiscriminant.lean) | Transformed restricted discriminant divides the original one |
| [AffineWeights](NairTenenbaum/Progressions/AffineWeights.lean) | Exact weight identity with the progression coprimality restriction |
| [ValueBoundContributions](NairTenenbaum/Contributions/ValueBoundContributions.lean) | All four majorants under a direct bound on polynomial values |
| [IntegerIntervalDecomposition](NairTenenbaum/Contributions/IntegerIntervalDecomposition.lean) | Exhaustive four-contribution cover on arbitrary integer intervals |
| [IntegerIntervalBound](NairTenenbaum/Contributions/IntegerIntervalBound.lean) | Common integer-interval bound with growth margin 17gε/24 and the all-scales progression specialization |
| [ProgressionIntervals](NairTenenbaum/Progressions/ProgressionIntervals.lean) | Progression reindexing and exact main-term identity |
| [ProgressionBound](NairTenenbaum/Progressions/ProgressionBound.lean) | Progression estimate at the original scale, with a height threshold independent of β |
| [CorollaryOne](NairTenenbaum/Results/CorollaryOne.lean) | Proposition `CorollaryOne` and proof `corollaryOne` |
| [IrreducibleSystem](NairTenenbaum/Polynomials/IrreducibleSystem.lean) | Identity-exponent factorization data, primitivity from the no-fixed-prime condition, and transfer of integral irreducibility |
| [IrreducibleProgressionWeights](NairTenenbaum/Polynomials/IrreducibleProgressionWeights.lean) | Exact tuple reindexing of the progression main term at every real cutoff |
| [CorollaryTwo](NairTenenbaum/Results/CorollaryTwo.lean) | Equation (20), with factorization data constructed from the polynomial hypotheses |
| [ProductArithmetic](NairTenenbaum/Arithmetic/ProductArithmetic.lean) | Admissibility of products with parameter B^k and compatibility with zero extension |
| [DivisorTupleDisjointness](NairTenenbaum/Arithmetic/DivisorTupleDisjointness.lean) | Distinct dagger tuples of equal weighted mass cannot divide the same factor values |
| [JointDensityComparison](NairTenenbaum/Sieve/JointDensityComparison.lean) | Density comparison for finite disjoint congruence families, deduced from CRT interval counts |
| [SubstitutionDensity](NairTenenbaum/Polynomials/SubstitutionDensity.lean) | Disjoint exponent supports and aggregation of root densities over substitution fibers |
| [FactoredWeightBound](NairTenenbaum/Arithmetic/FactoredWeightBound.lean) | Full weight sum bounded by the product of original-polynomial root-weighted sums |
| [CorollaryThree](NairTenenbaum/Results/CorollaryThree.lean) | Corollary 3 with uniform constants in the factorization interface |
| [FamilyFactorization](NairTenenbaum/Polynomials/FamilyFactorization.lean) | Construction of all factorization data for arbitrary admissible integer polynomial families |
| [FamilyTheorems](NairTenenbaum/Results/FamilyTheorems.lean) | Theorem 1 and Corollaries 1 and 3 for original polynomials, with no factorization-data hypothesis |
| [TheoremThree](NairTenenbaum/Results/TheoremThree.lean) | Theorem 3 with its original growth and interval hypotheses and explicit constant-term correction |
| [PrimeFamilyTheorem](NairTenenbaum/Results/PrimeFamilyTheorem.lean) | Theorem 3 for original polynomial families, with constructed factorization data |
| [ShiftedLinearSystem](NairTenenbaum/Polynomials/ShiftedLinearSystem.lean) | Exact height, discriminant, and weight for `X+a`; its prime main term bounded by the shifted-prime expression |
| [CorollarySeven](NairTenenbaum/Results/CorollarySeven.lean) | Shifted-prime estimate with both constants uniform in the nonzero shift |
| [GoldbachSieve](NairTenenbaum/DivisorSums/GoldbachSieve.lean) | Two-prime sieve with explicit reciprocal-totient correction and separate small-prime exceptions |
| [GoldbachScales](NairTenenbaum/DivisorSums/GoldbachScales.lean) | Uniform cutoff choice and logarithm-squared bound for lengths at least `N^θ` |
| [CorollaryTen](NairTenenbaum/Results/CorollaryTen.lean) | Goldbach bound with one prime in `(x,x+y]` under the original hypotheses |
| [SelectedMoment](NairTenenbaum/Smooth/SelectedMoment.lean) | Small-prime moments on the full truncated weight sum, including nonsmooth integers |
| [SelectedTilt](NairTenenbaum/Smooth/SelectedTilt.lean) | Complete multiplicativity of the selected moment and admissibility of the coordinate tilt |
| [SelectedTiltComparison](NairTenenbaum/Smooth/SelectedTiltComparison.lean) | Corrected proof of (41) with degree and restricted-discriminant uniformity |
| [PolynomialPreimages](NairTenenbaum/Polynomials/PolynomialPreimages.lean) | Coefficient-independent counts for prescribed and small absolute polynomial values |
| [FixedSmoothCounting](NairTenenbaum/Arithmetic/FixedSmoothCounting.lean) | Arbitrarily small power bounds for values supported on a fixed finite prime set |
| [SmoothValueRankin](NairTenenbaum/Smooth/SmoothValueRankin.lean) | Smoothness saving after separating small polynomial values, with zero extension preserved |
| [SmoothValueExceptional](NairTenenbaum/Smooth/SmoothValueExceptional.lean) | Weighted small-value and fixed-prime-support estimates for a nonconstant coordinate |
| [SmoothValueScales](NairTenenbaum/Smooth/SmoothValueScales.lean) | Uniform value bounds and absorption of exceptional terms under the original interval hypotheses |
| [SmoothValuePowerBounds](NairTenenbaum/Smooth/SmoothValuePowerBounds.lean) | Exceptional weighted sums bounded by a small power of the interval scale |
| [SmoothTiltBound](NairTenenbaum/Smooth/SmoothTiltBound.lean) | Theorem 1 applied to the selected-prime tilt, with uniform comparison to the original main term |
| [CorollarySix](NairTenenbaum/Results/CorollarySix.lean) | Exponential smoothness saving for a nonconstant restricted coordinate |
| [SmoothFamilyTheorem](NairTenenbaum/Results/SmoothFamilyTheorem.lean) | Corollary 6 for original polynomial families, with factorization constructed |
| [ConstantCoordinate](NairTenenbaum/Counterexamples/ConstantCoordinate.lean) | The family `(X,1)`, its exact smooth sum, and an upper bound for its main term |
| [CorollarySixObstruction](NairTenenbaum/Counterexamples/CorollarySixObstruction.lean) | Counterexample to dropping nonconstancy of the restricted polynomial |
| [DivisorSumRearrangement](NairTenenbaum/Arithmetic/DivisorSumRearrangement.lean) | Exact floor-sum identity and its uniform bound by a short sum of Hooley's function |
| [HooleyShortSum](NairTenenbaum/Hooley/HooleyShortSum.lean) | Polynomial Hooley moments reduced to root-weighted means for every positive interval exponent |
| [PrimeProgressionRearrangement](NairTenenbaum/Arithmetic/PrimeProgressionRearrangement.lean) | Exact averaged progression identity and its bound by Hooley's function at shifted primes |
| [HooleyPrimeShortSum](NairTenenbaum/Hooley/HooleyPrimeShortSum.lean) | Shifted-prime Hooley moments, including the uniform range `1≤|a|≤x` |
| [HooleyAverageReductions](NairTenenbaum/Hooley/HooleyAverageReductions.lean) | Corollaries 5 and 9 reduced to the same reciprocal Hooley mean, uniformly in the dyadic cutoff |
| [HooleyMoments](NairTenenbaum/Hooley/HooleyMoments.lean) | Integral moments, window measurability and integrability, and the divisor-count upper bound |
| [HooleyMomentComparison](NairTenenbaum/Hooley/HooleyMomentComparison.lean) | Maximum-to-moment comparison with factor `2^(q-1)` and positivity |
| [HooleyMomentRecurrence](NairTenenbaum/Hooley/HooleyMomentRecurrence.lean) | Exact coprime prime recurrence and mixed moments |
| [HooleyMomentInterpolation](NairTenenbaum/Hooley/HooleyMomentInterpolation.lean) | Interpolation between the first and higher moments, including mixed products |
| [PrimeLogIntervals](NairTenenbaum/Arithmetic/PrimeLogIntervals.lean) | Uniform logarithmic prime mass on intervals of fixed logarithmic length |
| [HooleyPrimeSampling](NairTenenbaum/Hooley/HooleyPrimeSampling.lean) | Finite weighted sampling bound for translated divisor windows |
| [HooleyPrimeMixedBound](NairTenenbaum/Hooley/HooleyPrimeMixedBound.lean) | Prime-summed mixed-moment bound with explicit `4^q` dependence |
| [HooleyWeightedPrimeStep](NairTenenbaum/Hooley/HooleyWeightedPrimeStep.lean) | Root-weighted finite prime recurrence with an explicit mixed error |
| [WeightedMomentPowers](NairTenenbaum/Arithmetic/WeightedMomentPowers.lean) | Weighted concavity and fractional-power prime recurrence |
| [HooleyDirichletCoefficients](NairTenenbaum/Hooley/HooleyDirichletCoefficients.lean) | Squarefree moment coefficients and subpolynomial bounds uniform in moment order |
| [HooleyDirichletSeries](NairTenenbaum/Hooley/HooleyDirichletSeries.lean) | Convergence of the moment Dirichlet series and its logarithmic companion for `σ>1` |
| [HooleyDirichletDerivative](NairTenenbaum/Hooley/HooleyDirichletDerivative.lean) | Termwise differentiation with a proved summable majorant |
| [PrimeFactorReindex](NairTenenbaum/Arithmetic/PrimeFactorReindex.lean) | Convergent reindexing from squarefree logarithmic sums to primes and positive cofactors |
| [HooleyDirichletPrimeExpansion](NairTenenbaum/Hooley/HooleyDirichletPrimeExpansion.lean) | Exact prime expansion of the Dirichlet derivative with squarefree and coprimality conditions |
| [HooleyInfinitePrimeStep](NairTenenbaum/Hooley/HooleyInfinitePrimeStep.lean) | Convergence of the root-weighted prime series and the infinite fractional-moment prime step |
| [SeriesInterpolation](NairTenenbaum/Arithmetic/SeriesInterpolation.lean) | Hölder interpolation of nonnegative convergent series |
| [HooleyDirichletError](NairTenenbaum/Hooley/HooleyDirichletError.lean) | Summable mixed error with nonlinear interpolation between divisor and moment series |
| [HooleyDifferentialInequality](NairTenenbaum/Hooley/HooleyDifferentialInequality.lean) | Unconditional differential inequality with explicit prime and divisor series |
| [SquarefreeEulerBound](NairTenenbaum/Arithmetic/SquarefreeEulerBound.lean) | Finite squarefree Euler bound and convergence from summable nonnegative prime weights |
| [HooleyDivisorEulerBound](NairTenenbaum/Hooley/HooleyDivisorEulerBound.lean) | Divisor Dirichlet series bounded by the exponential of `2^t` times the prime root series |
| [RootPrimeSeriesDerivative](NairTenenbaum/Arithmetic/RootPrimeSeriesDerivative.lean) | Derivative and finite-interval integral identities relating the two prime root series |
| [DifferentialInterpolation](NairTenenbaum/Arithmetic/DifferentialInterpolation.lean) | Integrating factor for the nonlinear differential inequality |
| [HooleyIntegratingFactor](NairTenenbaum/Hooley/HooleyIntegratingFactor.lean) | Transformed derivative bounded using only prime series and explicit constants |
| [HooleyIntegratedBound](NairTenenbaum/Hooley/HooleyIntegratedBound.lean) | Unconditional endpoint-plus-integral bound for the transformed moment series |
| [PrimeDirichletPoleBound](NairTenenbaum/Arithmetic/PrimeDirichletPoleBound.lean) | Elementary degree-uniform pole bound for the logarithmically weighted prime series |
| [ResidueHomKernels](NairTenenbaum/NumberFields/ResidueHomKernels.lean) | Residue homomorphisms are determined by their kernels, with exact quotient cardinality |
| [ConductorQuotient](NairTenenbaum/NumberFields/ConductorQuotient.lean) | Polynomial quotient description for every modulus coprime to the conductor exponent |
| [NumberFieldResidueRoots](NairTenenbaum/NumberFields/NumberFieldResidueRoots.lean) | Injective construction of ideals from minimal-polynomial residue roots |
| [IdealNormDirichlet](NairTenenbaum/NumberFields/IdealNormDirichlet.lean) | Convergent real ideal-norm series, Dedekind zeta identity, and simple-pole bound |
| [ConductorNonzero](NairTenenbaum/NumberFields/ConductorNonzero.lean) | Discriminant argument proving the conductor exponent is nonzero |
| [MinpolyEulerProduct](NairTenenbaum/NumberFields/MinpolyEulerProduct.lean) | Good-prime root Euler product bounded by the ideal-norm series |
| [PrimeProductLogBound](NairTenenbaum/Arithmetic/PrimeProductLogBound.lean) | Uniformly summable quadratic error between prime sums and logarithms of Euler products |
| [MinpolyPrimeLogBound](NairTenenbaum/NumberFields/MinpolyPrimeLogBound.lean) | Sharp logarithmic bound for the prime root series of an integral primitive generator |
| [IntegralRootNormalization](NairTenenbaum/NumberFields/IntegralRootNormalization.lean) | Integral primitive generator and residue-root comparison for a general integer polynomial |
| [IrreduciblePrimeLogBound](NairTenenbaum/NumberFields/IrreduciblePrimeLogBound.lean) | Sharp prime-root logarithmic bound for every integer polynomial irreducible over ℚ |
| [HooleyExponentGap](NairTenenbaum/Hooley/HooleyExponentGap.lean) | Positive exponent gap with lower bound `t/(7q(q−1))` for `t≥1` and `q≥2t` |
| [HooleyPowerMajorant](NairTenenbaum/Hooley/HooleyPowerMajorant.lean) | Explicit power majorant with constants chosen uniformly in moment order |
| [HooleyIntegratedPowerBound](NairTenenbaum/Hooley/HooleyIntegratedPowerBound.lean) | Integrated power estimate retaining the exact exponent-gap dependence |
| [HooleyMomentRecovery](NairTenenbaum/Hooley/HooleyMomentRecovery.lean) | Recovery of the original series with exponent `2^t−t+t/q` |
| [HooleyMomentOrderConstants](NairTenenbaum/Hooley/HooleyMomentOrderConstants.lean) | Integrated coefficient bounded linearly in the moment order |
| [HooleyDirichletPowerBound](NairTenenbaum/Hooley/HooleyDirichletPowerBound.lean) | Uniform bound `(Kq)^q (σ−1)^(−(2^t−t+t/q))` |
| [HooleySquarefreeRankin](NairTenenbaum/Hooley/HooleySquarefreeRankin.lean) | Finite squarefree reciprocal sums bounded by moment Dirichlet series |
| [HooleySquarefreePowerBound](NairTenenbaum/Hooley/HooleySquarefreePowerBound.lean) | Logarithmic finite-sum bound with moment-independent cutoff |
| [MomentOrderOptimization](NairTenenbaum/Smooth/MomentOrderOptimization.lean) | Rounded moment order and the sharp limiting coefficient `sqrt(2t)` |
| [HooleySquarefreeMean](NairTenenbaum/Hooley/HooleySquarefreeMean.lean) | Sharp reciprocal Hooley mean over squarefree integers |
| [RootCountSubpolynomial](NairTenenbaum/Polynomials/RootCountSubpolynomial.lean) | Subpolynomial root-count bounds for irreducible polynomials |
| [PowerfulDecomposition](NairTenenbaum/Arithmetic/PowerfulDecomposition.lean) | Coprime squarefree and powerful decomposition and square-times-cube representation |
| [PowerfulSummability](NairTenenbaum/Arithmetic/PowerfulSummability.lean) | Convergence of divisor-weighted root sums over powerful integers |
| [HooleyPowerfulComparison](NairTenenbaum/Hooley/HooleyPowerfulComparison.lean) | Unrestricted Hooley mean bounded by its squarefree counterpart |
| [HooleyWeightedMean](NairTenenbaum/Hooley/HooleyWeightedMean.lean) | Sharp unrestricted reciprocal Hooley mean with coefficient sqrt(2t) |
| [CorollaryFive](NairTenenbaum/Results/CorollaryFive.lean) | Corollary 5 with constants uniform in the dyadic cutoff |
| [PrimeReciprocalLogBound](NairTenenbaum/Arithmetic/PrimeReciprocalLogBound.lean) | Logarithmic upper bound for finite sums of prime reciprocals |
| [TotientLogLogBound](NairTenenbaum/Arithmetic/TotientLogLogBound.lean) | Reciprocal totients bounded by a fixed power of log log x |
| [TotientSubexponential](NairTenenbaum/Arithmetic/TotientSubexponential.lean) | Absorption of reciprocal totients into any positive Hooley exponent margin |
| [HooleyTotientMean](NairTenenbaum/Hooley/HooleyTotientMean.lean) | Sharp Hooley mean with a uniform reciprocal-totient factor |
| [CorollaryEight](NairTenenbaum/Results/CorollaryEight.lean) | Corollary 8 with both inequalities uniform in nonzero shifts up to x |
| [CorollaryNine](NairTenenbaum/Results/CorollaryNine.lean) | Corollary 9 uniform in the dyadic cutoff and nonzero residues up to x |
| [NumberFieldPrimeNormRoots](NairTenenbaum/NumberFields/NumberFieldPrimeNormRoots.lean) | Exact equality of good-prime residue-root counts and prime-norm ideal counts |
| [FiniteGeometricProduct](NairTenenbaum/Arithmetic/FiniteGeometricProduct.lean) | Finite sums encoded by independent geometric exponents |
| [IdealFiniteEulerBound](NairTenenbaum/NumberFields/IdealFiniteEulerBound.lean) | Ideal-factorization injection and geometric Euler bound |
| [PrimeIdealNormBounds](NairTenenbaum/NumberFields/PrimeIdealNormBounds.lean) | Prime-ideal norms and the degree bound on primes above a rational prime |
| [PrimeIdealErrorBounds](NairTenenbaum/NumberFields/PrimeIdealErrorBounds.lean) | Convergent quadratic errors from prime ideals of higher residue degree |
| [PrimeIdealRootComparison](NairTenenbaum/NumberFields/PrimeIdealRootComparison.lean) | Degree-one prime ideals compared with polynomial residue roots |
| [IdealRootEulerBound](NairTenenbaum/NumberFields/IdealRootEulerBound.lean) | Full ideal-norm series bounded above by the root Euler exponential |
| [MinpolyPrimeLowerBound](NairTenenbaum/NumberFields/MinpolyPrimeLowerBound.lean) | Sharp lower logarithmic bound for the minimal-polynomial prime-root series |
| [RootNormalizationEquality](NairTenenbaum/NumberFields/RootNormalizationEquality.lean) | Exact residue-root equality under integral normalization at good primes |
| [IrreduciblePrimeLowerBound](NairTenenbaum/NumberFields/IrreduciblePrimeLowerBound.lean) | Sharp lower logarithmic bound for irreducible-polynomial prime-root series |
| [PrimeRootReciprocalLowerBound](NairTenenbaum/NumberFields/PrimeRootReciprocalLowerBound.lean) | Truncated prime-root reciprocal sum bounded below by log log x minus a constant |
| [IrreducibleSieveProduct](NairTenenbaum/NumberFields/IrreducibleSieveProduct.lean) | Irreducible-polynomial sieve product bounded by a constant divided by log x |
| [CorollaryFour](NairTenenbaum/Results/CorollaryFour.lean) | Corollary 4 for every moment order at least one and every positive interval exponent |

## Conventions and scope

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
* Corollary 7 uses `x^(4ε) ≤ y ≤ x`, as inherited from Theorem 3. The printed
  corollary transposes `x` and `y` in this interval condition.

[BLUEPRINT.md](BLUEPRINT.md) records the proof dependencies and source corrections.
The repository directory can be renamed without changing the `NairTenenbaum`
namespace or imports; the build has no absolute-path dependencies.

| Module | Additional proved component |
| --- | --- |
| [IdealNormMultiplicative](NairTenenbaum/NumberFields/IdealNormMultiplicative.lean) | Unique factorization into ideals of specified coprime norms and multiplicativity of their counts |
| [ConvolutionMean](NairTenenbaum/NumberFields/ConvolutionMean.lean) | Exact convolution summatory identity and transfer of linear means under absolute summability |
| [IdealNormMean](NairTenenbaum/NumberFields/IdealNormMean.lean) | Multiplicative ideal-count arithmetic function, its positive mean, and convolution mean formula |
| [DyadicMeanDensity](NairTenenbaum/Arithmetic/DyadicMeanDensity.lean) | Positive means imply dyadic weighted lower bounds, including a root-count minorant interface |
| [MultiplicativeCompletion](NairTenenbaum/Arithmetic/MultiplicativeCompletion.lean) | Multiplicative extension of prime-power data and multiplicativity of Dirichlet inverses |
| [RootIdealCorrection](NairTenenbaum/NumberFields/RootIdealCorrection.lean) | Exact squarefree-root/ideal convolution correction and cancellation of its good-prime coefficients |
| [IdealPrimePowerCountBound](NairTenenbaum/NumberFields/IdealPrimePowerCountBound.lean) | Ideal counts of norm `p^k` bounded by `(k+1)^[K:ℚ]` |
| [DirichletInverseGrowth](NairTenenbaum/NumberFields/DirichletInverseGrowth.lean) | Uniform exponential bounds for local inverse and convolution coefficients |
| [RootIdealCorrectionGrowth](NairTenenbaum/NumberFields/RootIdealCorrectionGrowth.lean) | Explicit exponential coefficient bound for the correction of a primitive polynomial |
| [RootIdealCorrectionTail](NairTenenbaum/NumberFields/RootIdealCorrectionTail.lean) | Summable `O(1/p²)` positive-exponent tails at sufficiently large good primes |
| [PrimeIdealSupport](NairTenenbaum/NumberFields/PrimeIdealSupport.lean) | Canonical finite support of prime ideals above a rational prime |
| [IdealMultiplicityVectors](NairTenenbaum/NumberFields/IdealMultiplicityVectors.lean) | Exact bijection between ideals of prime-power norm and weighted multiplicity vectors |
| [WeightedGeometricPolynomial](NairTenenbaum/Arithmetic/WeightedGeometricPolynomial.lean) | Finite geometric polynomial coefficients count weighted multiplicity vectors |
| [IdealLocalEulerPolynomial](NairTenenbaum/NumberFields/IdealLocalEulerPolynomial.lean) | Polynomial inverse of the local ideal-counting series at every prime |
| [RootIdealLocalPolynomial](NairTenenbaum/NumberFields/RootIdealLocalPolynomial.lean) | Finite local correction with absolute summability and positive value at `1/p` |
| [EulerSummabilityCriterion](NairTenenbaum/NumberFields/EulerSummabilityCriterion.lean) | Global convergence of a multiplicative function from summable local tails |
| [RootIdealCorrectionPositive](NairTenenbaum/NumberFields/RootIdealCorrectionPositive.lean) | Positivity of the global correction assuming absolute convergence |
| [RootDensityFromIdealCounts](NairTenenbaum/NumberFields/RootDensityFromIdealCounts.lean) | Positive root mean from eventual agreement with prime-norm ideal counts |
| [IrreducibleRootDensity](NairTenenbaum/NumberFields/IrreducibleRootDensity.lean) | Positive mean and dyadic root-density lower bound for original irreducible polynomials |
| [PrimeIdealResidueDegree](NairTenenbaum/NumberFields/PrimeIdealResidueDegree.lean) | Residue-degree sum bound and exact description of prime-norm ideals |
| [ArithmeticLogDerivative](NairTenenbaum/NumberFields/ArithmeticLogDerivative.lean) | Logarithmic derivation, ideal von Mangoldt function, and exact convolution identity |
| [PowerSeriesEulerDerivative](NairTenenbaum/NumberFields/PowerSeriesEulerDerivative.lean) | Euler differentiation of formal power series and finite inverse products |
| [GeometricEulerDerivative](NairTenenbaum/NumberFields/GeometricEulerDerivative.lean) | Explicit logarithmic derivatives of weighted geometric series |
| [IdealVonMangoldtLocal](NairTenenbaum/NumberFields/IdealVonMangoldtLocal.lean) | Exact local von Mangoldt formula and prime-power degree bound |
| [ArithmeticLogDerivativeSupport](NairTenenbaum/NumberFields/ArithmeticLogDerivativeSupport.lean) | Prime-power support via multiplicativity in the square-zero extension |
| [IdealVonMangoldtBounds](NairTenenbaum/NumberFields/IdealVonMangoldtBounds.lean) | Nonnegativity, pointwise comparison, and linear Chebyshev bound |
| [IrreduciblePrimeIdealMatch](NairTenenbaum/NumberFields/IrreduciblePrimeIdealMatch.lean) | Eventual equality of original polynomial roots and prime-norm ideal counts |
| [PrimeRootMangoldtBound](NairTenenbaum/NumberFields/PrimeRootMangoldtBound.lean) | Weighted prime-root sum bounded by the ideal reciprocal sum plus a fixed constant |
| [SummatoryAbel](NairTenenbaum/Arithmetic/SummatoryAbel.lean) | Partial summation for arithmetic summatory functions |
| [SummatoryFractionalMoment](NairTenenbaum/Arithmetic/SummatoryFractionalMoment.lean) | Fractional moment bound from a linear summatory estimate |
| [ConvolutionPowerError](NairTenenbaum/NumberFields/ConvolutionPowerError.lean) | Linear convolution error from a power-saving summatory estimate |
| [LogWeightedSummatoryBound](NairTenenbaum/NumberFields/LogWeightedSummatoryBound.lean) | Logarithmic weighting with a linear error under a power-saving mean estimate |
| [IdealMangoldtMertensReduction](NairTenenbaum/NumberFields/IdealMangoldtMertensReduction.lean) | Conditional sharp Mertens bound from quantitative ideal counting |
| [LipschitzCubeCover](NairTenenbaum/Geometry/LipschitzCubeCover.lean) | Explicit mesh covers and covering cardinalities for dilated Lipschitz cube images |
| [IntegerLatticeBallBound](NairTenenbaum/Geometry/IntegerLatticeBallBound.lean) | Uniform integer lattice-point bounds in balls and finite ball covers |
| [LatticePointsNearChart](NairTenenbaum/Geometry/LatticePointsNearChart.lean) | A fixed neighborhood of a dilated m-parameter chart contains O(t^m) lattice points |
| [IntegerLatticeCells](NairTenenbaum/Geometry/IntegerLatticeCells.lean) | Unit-cell partition, exact volumes, and a finite cell-sandwich discrepancy bound |
| [IntegerLatticeBoundary](NairTenenbaum/Geometry/IntegerLatticeBoundary.lean) | Every bounded region has lattice discrepancy bounded by mixed boundary cells |
| [LipschitzBoundaryLatticeCount](NairTenenbaum/Geometry/LipschitzBoundaryLatticeCount.lean) | Quantitative lattice discrepancy for finitely many Lipschitz boundary charts |
| [NormLeOneBoundaryRadii](NairTenenbaum/Geometry/NormLeOneBoundaryRadii.lean) | Radial and unit-coordinate endpoint description of the norm-one boundary |
| [MixedPolarCoordinates](NairTenenbaum/Geometry/MixedPolarCoordinates.lean) | Signs and compact angular coordinates in mixed embedding space |
| [NormLeOneRadialCharts](NairTenenbaum/Geometry/NormLeOneRadialCharts.lean) | Smooth full-dimensional charts and their boundary-face representation |
| [CubeFaces](NairTenenbaum/Geometry/CubeFaces.lean) | Smooth lower-dimensional parametrizations of coordinate cube faces |
| [NormLeOneBoundaryCharts](NairTenenbaum/Geometry/NormLeOneBoundaryCharts.lean) | Finite smooth boundary charts and quantitative lattice count for the norm-one region |
| [LatticeCoordinateCount](NairTenenbaum/Geometry/LatticeCoordinateCount.lean) | Exact conversion of arbitrary integral-basis lattice counts to integer coordinates |
| [NormConeLatticePowerError](NairTenenbaum/Geometry/NormConeLatticePowerError.lean) | Power-saving fundamental-cone lattice count with exponent (degree-1)/degree |
| [IdealClassPowerError](NairTenenbaum/NumberFields/IdealClassPowerError.lean) | Power-saving counts in every ideal class, including torsion multiplicity and norm scaling |
| [PowerErrorMean](NairTenenbaum/NumberFields/PowerErrorMean.lean) | Identification of a power-saving count’s leading coefficient from its qualitative mean |
| [IdealNormPowerError](NairTenenbaum/NumberFields/IdealNormPowerError.lean) | Quantitative ideal count with the Dedekind zeta residue as leading coefficient |
| [PrimeRootMertens](NairTenenbaum/NumberFields/PrimeRootMertens.lean) | Unconditional sharp weighted prime-root bound log(x)+O(1) |
| [PolynomialSmoothLogEstimate](NairTenenbaum/Polynomials/PolynomialSmoothLogEstimate.lean) | Small-prime logarithmic mass bounded by y log(y)+O(y) |
| [TheoremTwoRoughMass](NairTenenbaum/Results/TheoremTwoRoughMass.lean) | Rough logarithmic mass with a linear error and exact interval cardinality |
| [TheoremTwoValueBounds](NairTenenbaum/Results/TheoremTwoValueBounds.lean) | Fixed polynomial-value and prime-cutoff constants for Theorem 2 |
| [TheoremTwoLogGain](NairTenenbaum/Results/TheoremTwoLogGain.lean) | Linear-error absorption and the strict exponent margin |
| [TheoremTwo](NairTenenbaum/Results/TheoremTwo.lean) | Full Theorem 2 under the original irreducible-polynomial hypotheses |
