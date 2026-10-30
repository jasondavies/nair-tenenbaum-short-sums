# Short sums of certain arithmetic functions

A Lean 4 / Mathlib formalization of

> M. Nair and G. Tenenbaum, *Short sums of certain arithmetic functions*,
> Acta Mathematica **180** (1998), 119–144.

[Author's PDF](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf) ·
[DOI](https://doi.org/10.1007/BF02392880)

Registered with Palomar as
[PALOMAR-2026-10-30-000010, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000010&version=1).

**Theorems 1–3, Corollaries 1–10, and Lemma 2 have Lean proofs**, with the
corrections and scope conventions listed below. The printed Lemma 1 has a checked
counterexample; the comparisons needed by the main results are proved separately.
Corollary 6 requires a nonconstant restricted polynomial.

The [statement map](#paper-statements) links every numbered result to its proof.
The `*_for_families` declarations construct factorization data from the original
integer polynomials. For proof dependencies and explanations of the source
corrections, see [BLUEPRINT.md](BLUEPRINT.md) and the
[completion audit](docs/completion-audit.yaml).

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
bash scripts/verify-comparator.sh   # requires Bubblewrap and permitted user/network namespaces
```

The recorded verification on 2026-10-30 audited **3,039 declarations**, with no
build warnings outside Challenge and no unused-argument lint errors.
`CheckStatements.lean` found exact agreement of all **14 theorem types** and
**19,610 transitive statement constants**. Comparator exported the proofs, and
**con-ron, NanoDa, and Lean's default kernel** accepted the solution.
[CI](.github/workflows/ci.yml) runs these checks and validates the submission
metadata against its schema.

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
| Corollary 7 | [`corollarySeven`](NairTenenbaum/Results/CorollarySeven.lean) | Corrects the transposed interval inequality to `x^(4ε) ≤ y ≤ x` |
| Corollary 8 | [`corollaryEight`](NairTenenbaum/Results/CorollaryEight.lean) | Uniform for `1 ≤ \|a\| ≤ x` |
| Corollary 9 | [`corollaryNine`](NairTenenbaum/Results/CorollaryNine.lean) | Makes explicit the inherited range `1 ≤ \|a\| ≤ x`; eventually covers each fixed nonzero residue |
| Corollary 10 | [`corollaryTen`](NairTenenbaum/Results/CorollaryTen.lean) | Uniform short-interval Goldbach upper bound |
| Lemma 1 | [`LemmaOneObstruction.linearSystem_comparison_fails`](NairTenenbaum/Counterexamples/LemmaOneCounterexample.lean) | Printed comparison refuted; required [totient](NairTenenbaum/Arithmetic/ComparisonUniformity.lean) and [selected-prime](NairTenenbaum/Smooth/SelectedTiltComparison.lean) replacements proved |
| Lemma 2 | [`lemmaTwo`](NairTenenbaum/Results/LemmaTwo.lean) | General class-`M` weights, original cutoff, convergence, and uniform constant |

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
For submission instructions, see [Palomar](https://palomar-registry.org/how-to-submit).
The project uses the conventional configuration paths at the repository root.
The [Apache-2.0 license](LICENSE) applies to this repository, not to the cited papers.

## Library layout

The public namespace is `NairTenenbaum`. Individual module imports use the
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

## Module index

All 353 library modules are listed below, grouped by folder and alphabetized
within each group. Expand a folder to browse its modules; the
[blueprint](BLUEPRINT.md) presents them in proof order.

<details>
<summary>Arithmetic (65 modules)</summary>

| Module | Content |
| --- | --- |
| [AppendArithmetic](NairTenenbaum/Arithmetic/AppendArithmetic.lean) | Products on independent coordinate blocks; scalar class `M` and common constants |
| [Arithmetic](NairTenenbaum/Arithmetic/Arithmetic.lean) | Positive tuples; `Ω`; equation (1); parameter monotonicity; addition, scaling and real powers; vanishing when `F(1)=0` |
| [AuxiliaryFunctions](NairTenenbaum/Arithmetic/AuxiliaryFunctions.lean) | The multiplicative functions `f_h`, local geometric bounds, and the arbitrary-tuple bound (17) |
| [AuxiliarySeries](NairTenenbaum/Arithmetic/AuxiliarySeries.lean) | Convergence and tails of the local series; the finite Euler product over smooth integers |
| [ComparisonKernel](NairTenenbaum/Arithmetic/ComparisonKernel.lean) | Kernel Euler products and a global scalar comparison with a constant independent of the cutoff |
| [ComparisonLocal](NairTenenbaum/Arithmetic/ComparisonLocal.lean) | Root-weighted tail bounds, a sufficient local comparison criterion, and bounded finite Euler products |
| [ComparisonUniformity](NairTenenbaum/Arithmetic/ComparisonUniformity.lean) | Comparison constant depending only on degree, growth parameters, and restricted discriminant |
| [CompleteResidueBlock](NairTenenbaum/Arithmetic/CompleteResidueBlock.lean) | Complete residue blocks inside real short intervals |
| [CongruenceCount](NairTenenbaum/Arithmetic/CongruenceCount.lean) | Counts in integer intervals: the error from `(b-a)ρ_Q(q)/q` is at most `ρ_Q(q)`, for every positive modulus |
| [DifferentialInterpolation](NairTenenbaum/Arithmetic/DifferentialInterpolation.lean) | Integrating factor for the nonlinear differential inequality |
| [DivisorBounds](NairTenenbaum/Arithmetic/DivisorBounds.lean) | `τ(n) ≤ 2^Ω(n)`; `τ(n) ≪_ε n^ε`; admissibility of `Δ` and every positive real power of `Δ` |
| [DivisorSumRearrangement](NairTenenbaum/Arithmetic/DivisorSumRearrangement.lean) | Exact floor-sum identity and its uniform bound by a short sum of Hooley's function |
| [DivisorTupleDisjointness](NairTenenbaum/Arithmetic/DivisorTupleDisjointness.lean) | Distinct dagger tuples of equal weighted mass cannot divide the same factor values |
| [DyadicMeanDensity](NairTenenbaum/Arithmetic/DyadicMeanDensity.lean) | Positive means imply dyadic weighted lower bounds, including a root-count minorant interface |
| [FactoredWeightBound](NairTenenbaum/Arithmetic/FactoredWeightBound.lean) | Full weight sum bounded by the product of original-polynomial root-weighted sums |
| [FiniteGeometricProduct](NairTenenbaum/Arithmetic/FiniteGeometricProduct.lean) | Finite sums encoded by independent geometric exponents |
| [FixedSmoothCounting](NairTenenbaum/Arithmetic/FixedSmoothCounting.lean) | Arbitrarily small power bounds for values supported on a fixed finite prime set |
| [FloorRootArithmetic](NairTenenbaum/Arithmetic/FloorRootArithmetic.lean) | Coprime multiplicativity of prime-factor roots and preservation of scalar admissibility |
| [FractionalAuxiliary](NairTenenbaum/Arithmetic/FractionalAuxiliary.lean) | Convergent auxiliary series with fractional denominators and uniform finite smooth bounds |
| [MainTermLowerBound](NairTenenbaum/Arithmetic/MainTermLowerBound.lean) | Unit weight and uniform absorption of power-saving errors into the original main term |
| [MinimalMajorant](NairTenenbaum/Arithmetic/MinimalMajorant.lean) | Equation (11) as a supremum; equations (12)–(13); minimality, submultiplicativity, and admissibility of `G_F` |
| [MultiplicativeCompletion](NairTenenbaum/Arithmetic/MultiplicativeCompletion.lean) | Multiplicative extension of prime-power data and multiplicativity of Dirichlet inverses |
| [MultivariableComparison](NairTenenbaum/Arithmetic/MultivariableComparison.lean) | Corrected totient comparison for the full weight (16), all real cutoffs, and actual polynomial systems |
| [Normalization](NairTenenbaum/Arithmetic/Normalization.lean) | Homogeneity of sums and weights; reduction of a short-sum estimate to `F(1)=1`, with the estimate explicitly assumed |
| [PowerfulDecomposition](NairTenenbaum/Arithmetic/PowerfulDecomposition.lean) | Coprime squarefree and powerful decomposition and square-times-cube representation |
| [PowerfulSummability](NairTenenbaum/Arithmetic/PowerfulSummability.lean) | Convergence of divisor-weighted root sums over powerful integers |
| [PrimeDirichletPoleBound](NairTenenbaum/Arithmetic/PrimeDirichletPoleBound.lean) | Elementary degree-uniform pole bound for the logarithmically weighted prime series |
| [PrimeFactorBounds](NairTenenbaum/Arithmetic/PrimeFactorBounds.lean) | Uniform subpolynomial bounds for `K^ω(n)` and least-common-multiple majorants |
| [PrimeFactorReindex](NairTenenbaum/Arithmetic/PrimeFactorReindex.lean) | Convergent reindexing from squarefree logarithmic sums to primes and positive cofactors |
| [PrimeLogIntervals](NairTenenbaum/Arithmetic/PrimeLogIntervals.lean) | Uniform logarithmic prime mass on intervals of fixed logarithmic length |
| [PrimeLogSums](NairTenenbaum/Arithmetic/PrimeLogSums.lean) | Elementary logarithmic prime sums and cutoff-uniform bounds for `p^(κ/log z)-1` |
| [PrimeMajorant](NairTenenbaum/Arithmetic/PrimeMajorant.lean) | Prime-part decomposition of tuples and the full multivariable bound (14) |
| [PrimePowerComparison](NairTenenbaum/Arithmetic/PrimePowerComparison.lean) | Valuation-dependent prime increments and finite convolution with separate coordinate domains |
| [PrimePowerCounting](NairTenenbaum/Arithmetic/PrimePowerCounting.lean) | Elementary union bound for large powers of small primes, with density at most a constant times z/T |
| [PrimePowerLogCutoff](NairTenenbaum/Arithmetic/PrimePowerLogCutoff.lean) | A logarithmic cutoff for prime-power divisibility |
| [PrimePowerLogExpansion](NairTenenbaum/Arithmetic/PrimePowerLogExpansion.lean) | Prime-power divisibility counts in the smooth logarithmic mass |
| [PrimePowerRoots](NairTenenbaum/Arithmetic/PrimePowerRoots.lean) | Root reduction; vanishing at multiples of a root-free modulus; injectivity on simple roots; exponent-independent root bounds under separable reduction |
| [PrimePowerThreshold](NairTenenbaum/Arithmetic/PrimePowerThreshold.lean) | Least prime power above a threshold and large coordinate prime powers forced by a prefix crossing |
| [PrimeProductLogBound](NairTenenbaum/Arithmetic/PrimeProductLogBound.lean) | Uniformly summable quadratic error between prime sums and logarithms of Euler products |
| [PrimeProgressionRearrangement](NairTenenbaum/Arithmetic/PrimeProgressionRearrangement.lean) | Exact averaged progression identity and its bound by Hooley's function at shifted primes |
| [PrimeReciprocalLogBound](NairTenenbaum/Arithmetic/PrimeReciprocalLogBound.lean) | Logarithmic upper bound for finite sums of prime reciprocals |
| [PrimeSplitting](NairTenenbaum/Arithmetic/PrimeSplitting.lean) | Full prime-part selection, cross-coordinate coprimality, exact factorizations, and (29)–(30) |
| [PrimeThreshold](NairTenenbaum/Arithmetic/PrimeThreshold.lean) | First prime crossing a real weighted-mass threshold, equation (28), and the small-total-mass alternative |
| [ProductArithmetic](NairTenenbaum/Arithmetic/ProductArithmetic.lean) | Admissibility of products with parameter B^k and compatibility with zero extension |
| [RootAuxiliary](NairTenenbaum/Arithmetic/RootAuxiliary.lean) | Root-weighted multiplicative majorants, local convergence and finite Euler products, with the polynomial hypotheses discharged |
| [RootPrimeSeriesDerivative](NairTenenbaum/Arithmetic/RootPrimeSeriesDerivative.lean) | Derivative and finite-interval integral identities relating the two prime root series |
| [RoughMass](NairTenenbaum/Arithmetic/RoughMass.lean) | Prime-factor count and arithmetic-growth bounds for rough remaining factors |
| [ScalarComparison](NairTenenbaum/Arithmetic/ScalarComparison.lean) | Corrected scalar totient comparison for admissible functions and the actual polynomial factors, with an explicit uniform constant |
| [ScalarPrimeSplit](NairTenenbaum/Arithmetic/ScalarPrimeSplit.lean) | Smooth and rough parts at a real cutoff |
| [SeriesInterpolation](NairTenenbaum/Arithmetic/SeriesInterpolation.lean) | Hölder interpolation of nonnegative convergent series |
| [SquarefreeEulerBound](NairTenenbaum/Arithmetic/SquarefreeEulerBound.lean) | Finite squarefree Euler bound and convergence from summable nonnegative prime weights |
| [SummatoryAbel](NairTenenbaum/Arithmetic/SummatoryAbel.lean) | Partial summation for arithmetic summatory functions |
| [SummatoryFractionalMoment](NairTenenbaum/Arithmetic/SummatoryFractionalMoment.lean) | Fractional moment bound from a linear summatory estimate |
| [TotientComparisonExponents](NairTenenbaum/Arithmetic/TotientComparisonExponents.lean) | Uniform comparison with an independent totient exponent |
| [TotientLogLogBound](NairTenenbaum/Arithmetic/TotientLogLogBound.lean) | Reciprocal totients bounded by a fixed power of log log x |
| [TotientProducts](NairTenenbaum/Arithmetic/TotientProducts.lean) | Totient corrections for arbitrary products and prime-support inclusions |
| [TotientSubexponential](NairTenenbaum/Arithmetic/TotientSubexponential.lean) | Absorption of reciprocal totients into any positive Hooley exponent margin |
| [TotientTwist](NairTenenbaum/Arithmetic/TotientTwist.lean) | Reciprocal-totient correction; its stronger weighted local condition for the actual polynomial factors |
| [TupleComparison](NairTenenbaum/Arithmetic/TupleComparison.lean) | Multivariable whole prime-power splitting and the finite kernel comparison |
| [UnitaryComparison](NairTenenbaum/Arithmetic/UnitaryComparison.lean) | Finite scalar comparison by an injective split into complementary whole prime-power factors |
| [ValueWeightBounds](NairTenenbaum/Arithmetic/ValueWeightBounds.lean) | Pointwise arithmetic-weight bound by a power of the mass |
| [WeightTruncation](NairTenenbaum/Arithmetic/WeightTruncation.lean) | Dagger preservation, cross-coprimality, weighted-mass cutoffs, and exact reindexing of finite weight sums |
| [WeightedGeometricPolynomial](NairTenenbaum/Arithmetic/WeightedGeometricPolynomial.lean) | Finite geometric polynomial coefficients count weighted multiplicity vectors |
| [WeightedMomentPowers](NairTenenbaum/Arithmetic/WeightedMomentPowers.lean) | Weighted concavity and fractional-power prime recurrence |
| [Weights](NairTenenbaum/Arithmetic/Weights.lean) | Exponent substitution, equations (15)–(16), both dagger restrictions, finiteness of fibers, and exact one-variable specialization |

</details>

<details>
<summary>Polynomials (25 modules)</summary>

| Module | Content |
| --- | --- |
| [DiscriminantBezout](NairTenenbaum/Polynomials/DiscriminantBezout.lean) | Bézout identity for the discriminant in degree at least two; simple residue roots away from the discriminant, including primes dividing the leading coefficient |
| [DiscriminantSplitting](NairTenenbaum/Polynomials/DiscriminantSplitting.lean) | Full discriminant-prime removal gives dagger tuples and a cross-coprime factorization; removed support lies in the restricted bad discriminant |
| [FamilyFactorization](NairTenenbaum/Polynomials/FamilyFactorization.lean) | Construction of all factorization data for arbitrary admissible integer polynomial families |
| [IrreducibleProgressionWeights](NairTenenbaum/Polynomials/IrreducibleProgressionWeights.lean) | Exact tuple reindexing of the progression main term at every real cutoff |
| [IrreducibleSystem](NairTenenbaum/Polynomials/IrreducibleSystem.lean) | Identity-exponent factorization data, primitivity from the no-fixed-prime condition, and transfer of integral irreducibility |
| [LinearCase](NairTenenbaum/Polynomials/LinearCase.lean) | An explicit `Q(X)=X` instance and the specialization of its weight and main term |
| [PolynomialHeight](NairTenenbaum/Polynomials/PolynomialHeight.lean) | Coefficient and value bounds in terms of the polynomial height and degree |
| [PolynomialLocal](NairTenenbaum/Polynomials/PolynomialLocal.lean) | Prime-power root bounds at all primes, uniformly by `max(deg R_h,D³)`; common value-divisors of distinct factors divide `D*` |
| [PolynomialLogMass](NairTenenbaum/Polynomials/PolynomialLogMass.lean) | Quantitative lower logarithmic mass of polynomial values |
| [PolynomialLogMassLength](NairTenenbaum/Polynomials/PolynomialLogMassLength.lean) | The total logarithmic mass with an explicit interval-length error |
| [PolynomialLogParts](NairTenenbaum/Polynomials/PolynomialLogParts.lean) | Canonical smooth and rough logarithmic masses of polynomial values |
| [PolynomialPreimages](NairTenenbaum/Polynomials/PolynomialPreimages.lean) | Coefficient-independent counts for prescribed and small absolute polynomial values |
| [PolynomialSieve](NairTenenbaum/Polynomials/PolynomialSieve.lean) | Polynomial-value sieve in integer intervals, with coefficient-independent constants and the congruence remainder discharged |
| [PolynomialSmoothLogEstimate](NairTenenbaum/Polynomials/PolynomialSmoothLogEstimate.lean) | Small-prime logarithmic mass bounded by y log(y)+O(y) |
| [PolynomialSmoothPrimeBound](NairTenenbaum/Polynomials/PolynomialSmoothPrimeBound.lean) | Small-prime logarithmic mass reduced to the weighted prime-root sum |
| [PolynomialStructure](NairTenenbaum/Polynomials/PolynomialStructure.lean) | Degree identities, bounds on the number of factors, rational separability, and nonzero discriminant of the radical |
| [PolynomialSystem](NairTenenbaum/Polynomials/PolynomialSystem.lean) | Equation (9), factorization data, discriminants, coefficient height, root vectors, short sums and the main term |
| [PolynomialValueBounds](NairTenenbaum/Polynomials/PolynomialValueBounds.lean) | Uniform power bound for polynomial values under the height hypothesis |
| [PolynomialValueTuples](NairTenenbaum/Polynomials/PolynomialValueTuples.lean) | Positive value tuples, exact weighted total value, and the sieve condition for selected prefixes |
| [PrimitivePrimePowerRoots](NairTenenbaum/Polynomials/PrimitivePrimePowerRoots.lean) | Uniform prime-power roots for primitive polynomials |
| [PrimitiveResidueRoots](NairTenenbaum/Polynomials/PrimitiveResidueRoots.lean) | Residue roots of primitive integral polynomials |
| [RootCount](NairTenenbaum/Polynomials/RootCount.lean) | Equation (10); CRT multiplicativity; prime root bound by degree; invariance under removing positive powers at primes; linear examples; positivity of the sieve product |
| [RootCountSubpolynomial](NairTenenbaum/Polynomials/RootCountSubpolynomial.lean) | Subpolynomial root-count bounds for irreducible polynomials |
| [ShiftedLinearSystem](NairTenenbaum/Polynomials/ShiftedLinearSystem.lean) | Exact height, discriminant, and weight for `X+a`; its prime main term bounded by the shifted-prime expression |
| [SubstitutionDensity](NairTenenbaum/Polynomials/SubstitutionDensity.lean) | Disjoint exponent supports and aggregation of root densities over substitution fibers |

</details>

<details>
<summary>Sieve (24 modules)</summary>

| Module | Content |
| --- | --- |
| [BadPrimeCongruence](NairTenenbaum/Sieve/BadPrimeCongruence.lean) | Uniform summation of bad-prime congruence contributions, including admissible arithmetic weights |
| [BadPrimeMass](NairTenenbaum/Sieve/BadPrimeMass.lean) | Least-common-multiple density and convergence of the full bad-prime tuple series, uniformly in degree and restricted discriminant |
| [BadPrimeMoments](NairTenenbaum/Sieve/BadPrimeMoments.lean) | Uniform positive moments of the full bad-prime tuple kernel, including every valuation |
| [BadPrimeRoots](NairTenenbaum/Sieve/BadPrimeRoots.lean) | Root clustering via Taylor expansion; `ρ_Q(p^ν) ≤ p^(2 v_p(discr Q)+1)` in degree at least two |
| [BadPrimeSieve](NairTenenbaum/Sieve/BadPrimeSieve.lean) | Conditional sieve with bad-part LCM density and uniform summation over every bad-prime valuation |
| [ConditionalPolynomialSieve](NairTenenbaum/Sieve/ConditionalPolynomialSieve.lean) | The global no-fixed-prime specialization of the local conditional sieve |
| [JointCongruence](NairTenenbaum/Sieve/JointCongruence.lean) | Exact CRT density and interval error for simultaneous polynomial congruences; mixed bad-part and good-coordinate counting bounds |
| [JointDensityComparison](NairTenenbaum/Sieve/JointDensityComparison.lean) | Density comparison for finite disjoint congruence families, deduced from CRT interval counts |
| [LocalConditionalSieve](NairTenenbaum/Sieve/LocalConditionalSieve.lean) | Conditional sieves using admissibility only at the selected primes |
| [OmittedEulerFactors](NairTenenbaum/Sieve/OmittedEulerFactors.lean) | Missing Euler factors bounded by `(n/φ(n))^g` times an explicit degree-only constant |
| [SelbergCoefficientBounds](NairTenenbaum/Sieve/SelbergCoefficientBounds.lean) | Uniform local and subpolynomial bounds for the optimized sieve coefficients |
| [SelbergDenominator](NairTenenbaum/Sieve/SelbergDenominator.lean) | Exact logarithmic moment and quantitative denominator bound: at least one quarter of the full Euler product at cutoff `z^(2g)` when `log z≥16` |
| [SelbergRemainder](NairTenenbaum/Sieve/SelbergRemainder.lean) | Quadratic remainder estimate and quantitative sieve upper bound with a constant depending only on dimension and the error exponent |
| [SelbergWeights](NairTenenbaum/Sieve/SelbergWeights.lean) | Optimized truncated Selberg coefficients, exact reciprocal-denominator main term, and remainder support through the square of the cutoff |
| [SieveCutoffComparison](NairTenenbaum/Sieve/SieveCutoffComparison.lean) | Uniform comparison of the sifting products at a power cutoff and the original cutoff |
| [SieveLevel](NairTenenbaum/Sieve/SieveLevel.lean) | Conditional sieve remainder absorbed under an explicit modulus-and-cutoff size condition |
| [SievePrimes](NairTenenbaum/Sieve/SievePrimes.lean) | Actual sieve prime product, omission of root-free and modulus primes, and restoration of the full sifting product |
| [SieveProductLowerBound](NairTenenbaum/Sieve/SieveProductLowerBound.lean) | Uniform bound `sieveProduct(Q,z)⁻¹ ≪ z^δ` for every positive exponent |
| [SieveScales](NairTenenbaum/Sieve/SieveScales.lean) | The paper’s small-divisor scales satisfy the sieve level uniformly in the polynomial coefficients |
| [SiftedDivisorSplit](NairTenenbaum/Sieve/SiftedDivisorSplit.lean) | Shared divisor splitting and fiber-counting proofs for integer and prime arguments |
| [SmallDivisorMainTerm](NairTenenbaum/Sieve/SmallDivisorMainTerm.lean) | The sifted small-divisor sum bounded by the original main term, with uniform constants |
| [SmallDivisorMajorant](NairTenenbaum/Sieve/SmallDivisorMajorant.lean) | Grouping selected prefixes by divisor tuple proves the first-contribution sieve majorant |
| [SmallDivisorSieve](NairTenenbaum/Sieve/SmallDivisorSieve.lean) | Summation over good tuples and removal of their totient correction |
| [SmallDivisorSum](NairTenenbaum/Sieve/SmallDivisorSum.lean) | Reindexing from the original divisor tuples and a single weighted-mass sieve level |

</details>

<details>
<summary>Smooth (44 modules)</summary>

| Module | Content |
| --- | --- |
| [GeneralSmoothTail](NairTenenbaum/Smooth/GeneralSmoothTail.lean) | Finite and convergent infinite tails for general admissible scalar weights |
| [LargePrefixMainTerm](NairTenenbaum/Smooth/LargePrefixMainTerm.lean) | Sifted large-prefix sum bounded by the original main term |
| [LargePrefixScales](NairTenenbaum/Smooth/LargePrefixScales.lean) | Uniform sieve level for prefixes up to x^(3g²ε) and prime cutoffs at most x^(gε/16) |
| [LiftedWeightSums](NairTenenbaum/Smooth/LiftedWeightSums.lean) | Smooth-tail and truncated-sum comparisons under the lift |
| [LiftedWeights](NairTenenbaum/Smooth/LiftedWeights.lean) | Doubled exponent matrix, squared mass, and exact encoding of scalar weights |
| [MomentKernel](NairTenenbaum/Smooth/MomentKernel.lean) | Convergent Euler product for the exponential-moment kernel and bounds for its smooth partial sums |
| [MomentOrderOptimization](NairTenenbaum/Smooth/MomentOrderOptimization.lean) | Rounded moment order and the sharp limiting coefficient `sqrt(2t)` |
| [MomentPrimeBounds](NairTenenbaum/Smooth/MomentPrimeBounds.lean) | A cutoff-uniform bound for root-weighted moment-correction Euler products, with the exponent gap and root bounds discharged |
| [PrimeBandBounds](NairTenenbaum/Smooth/PrimeBandBounds.lean) | Reciprocal prime sums and uniform root-auxiliary Euler products on a band of primes |
| [PrimeBandContribution](NairTenenbaum/Smooth/PrimeBandContribution.lean) | One-band estimate for the original arithmetic weights |
| [PrimeBandCover](NairTenenbaum/Smooth/PrimeBandCover.lean) | Actual prefixes assigned to eligible bands, including the finite-interval cover |
| [PrimeBandCutoff](NairTenenbaum/Smooth/PrimeBandCutoff.lean) | A fixed cutoff supplies every band condition; positive moment strength chosen before the polynomials |
| [PrimeBandDecay](NairTenenbaum/Smooth/PrimeBandDecay.lean) | Tail decay after paying arithmetic and Euler-product costs; dyadic band cover and geometric summation |
| [PrimeBandMajorant](NairTenenbaum/Smooth/PrimeBandMajorant.lean) | One-band sifted estimate with constants independent of the band index |
| [PrimeBandSummation](NairTenenbaum/Smooth/PrimeBandSummation.lean) | Uniform bound for any finite collection of eligible logarithmic bands |
| [RootSmoothTail](NairTenenbaum/Smooth/RootSmoothTail.lean) | Convergent infinite root-weighted smooth tail with the exponential saving and a right-hand sum truncated at `z` |
| [SelectedMoment](NairTenenbaum/Smooth/SelectedMoment.lean) | Small-prime moments on the full truncated weight sum, including nonsmooth integers |
| [SelectedTilt](NairTenenbaum/Smooth/SelectedTilt.lean) | Complete multiplicativity of the selected moment and admissibility of the coordinate tilt |
| [SelectedTiltComparison](NairTenenbaum/Smooth/SelectedTiltComparison.lean) | Corrected proof of (41) with degree and restricted-discriminant uniformity |
| [SmoothCutoffComparison](NairTenenbaum/Smooth/SmoothCutoffComparison.lean) | Comparison of two smoothness cutoffs with the dagger restrictions and mass bound preserved |
| [SmoothDivisorCounting](NairTenenbaum/Smooth/SmoothDivisorCounting.lean) | Large smooth divisor tuples mapped to one radical-value divisor through their least common multiple |
| [SmoothDivisorDensity](NairTenenbaum/Smooth/SmoothDivisorDensity.lean) | Reciprocal-density tail for smooth moduli and uniform radical root counts at every prime power |
| [SmoothLogCountingError](NairTenenbaum/Smooth/SmoothLogCountingError.lean) | A linear error for the small-prime logarithmic mass |
| [SmoothLogExpansion](NairTenenbaum/Smooth/SmoothLogExpansion.lean) | Exact logarithmic expansion of the smooth part |
| [SmoothLogHigherPowers](NairTenenbaum/Smooth/SmoothLogHigherPowers.lean) | Bounded higher-prime-power contributions to the logarithmic main term |
| [SmoothLogRootBound](NairTenenbaum/Smooth/SmoothLogRootBound.lean) | Root-density and remainder terms for the small-prime logarithmic mass |
| [SmoothMoment](NairTenenbaum/Smooth/SmoothMoment.lean) | Global finite moments and Rankin tails for smooth dagger tuples, uniform in both cutoffs |
| [SmoothMomentUniformity](NairTenenbaum/Smooth/SmoothMomentUniformity.lean) | Totient-modified smooth moments bounded by the original truncated weight sum with uniform constants |
| [SmoothTailMajorant](NairTenenbaum/Smooth/SmoothTailMajorant.lean) | Selected-prefix reduction retaining the original lower mass cutoff and smoothness support |
| [SmoothTailSieve](NairTenenbaum/Smooth/SmoothTailSieve.lean) | Conditional sieve on a smooth mass tail with separate smoothness and sifting cutoffs |
| [SmoothTailSieveReindex](NairTenenbaum/Smooth/SmoothTailSieveReindex.lean) | Original smooth divisor tail reindexed without losing its mass cutoff |
| [SmoothTailUniformity](NairTenenbaum/Smooth/SmoothTailUniformity.lean) | Positive smooth-tail constants depending only on growth parameters, degree and restricted discriminant; Theorem 1 parameter specialization |
| [SmoothTiltBound](NairTenenbaum/Smooth/SmoothTiltBound.lean) | Theorem 1 applied to the selected-prime tilt, with uniform comparison to the original main term |
| [SmoothTruncation](NairTenenbaum/Smooth/SmoothTruncation.lean) | Explicit smaller cutoff and absorption of its smooth tail |
| [SmoothTruncationUniform](NairTenenbaum/Smooth/SmoothTruncationUniform.lean) | Reduction of full finite smooth sums to mass at most `z`, for every `z≥2` |
| [SmoothValueExceptional](NairTenenbaum/Smooth/SmoothValueExceptional.lean) | Weighted small-value and fixed-prime-support estimates for a nonconstant coordinate |
| [SmoothValuePowerBounds](NairTenenbaum/Smooth/SmoothValuePowerBounds.lean) | Exceptional weighted sums bounded by a small power of the interval scale |
| [SmoothValueRankin](NairTenenbaum/Smooth/SmoothValueRankin.lean) | Smoothness saving after separating small polynomial values, with zero extension preserved |
| [SmoothValueScales](NairTenenbaum/Smooth/SmoothValueScales.lean) | Uniform value bounds and absorption of exceptional terms under the original interval hypotheses |
| [SmoothWeightSum](NairTenenbaum/Smooth/SmoothWeightSum.lean) | Exact reindexing into the paper's weight notation and the root-weighted smooth tail bound for polynomial systems |
| [SplitSmoothTail](NairTenenbaum/Smooth/SplitSmoothTail.lean) | Smooth-tail saving on the combined bad/good prefix mass |
| [TiltedAuxiliary](NairTenenbaum/Smooth/TiltedAuxiliary.lean) | Convergence and finite smooth Euler products after exponential tilting; exact local moment increments |
| [TiltedTotientComparison](NairTenenbaum/Smooth/TiltedTotientComparison.lean) | Corrected totient comparison after exponential tilting, uniform below a fixed convergence exponent |
| [TotientSmoothTail](NairTenenbaum/Smooth/TotientSmoothTail.lean) | Convergent totient-modified smooth tails bounded by the truncated original root weight |

</details>

<details>
<summary>Contributions (15 modules)</summary>

| Module | Content |
| --- | --- |
| [FirstContribution](NairTenenbaum/Contributions/FirstContribution.lean) | The small rough-prefix class and its reduction to the sifted divisor sum |
| [FirstContributionReal](NairTenenbaum/Contributions/FirstContributionReal.lean) | Real and positive integral cutoffs for the small rough-prefix predicate |
| [IntegerIntervalBound](NairTenenbaum/Contributions/IntegerIntervalBound.lean) | Common integer-interval bound with growth margin 17gε/24, and its all-scales form |
| [IntegerIntervalDecomposition](NairTenenbaum/Contributions/IntegerIntervalDecomposition.lean) | Exhaustive four-contribution cover on arbitrary integer intervals |
| [IntermediateContributionReal](NairTenenbaum/Contributions/IntermediateContributionReal.lean) | Real and positive integral cutoffs for the intermediate-prefix predicate |
| [RealIntervalBounds](NairTenenbaum/Contributions/RealIntervalBounds.lean) | Integer endpoint bounds and exact natural-to-integer interval reindexing |
| [SecondContribution](NairTenenbaum/Contributions/SecondContribution.lean) | Small-crossing-prime predicate, scale identity, and sieve-level bound |
| [SecondContributionCounting](NairTenenbaum/Contributions/SecondContributionCounting.lean) | Second-class inclusion in the exceptional set and degree/discriminant-uniform counting |
| [SecondContributionWeights](NairTenenbaum/Contributions/SecondContributionWeights.lean) | The weighted sum over the small-prime power exceptional set |
| [ShortIntervalCardinality](NairTenenbaum/Contributions/ShortIntervalCardinality.lean) | Rounding errors in the number of integers in a short interval |
| [ShortIntervalCongruenceUpper](NairTenenbaum/Contributions/ShortIntervalCongruenceUpper.lean) | Upper congruence counts with the rounding error retained |
| [ShortSumDecomposition](NairTenenbaum/Contributions/ShortSumDecomposition.lean) | Exhaustive four-majorant cover, including small total values and zero-extension terms |
| [ThirdContribution](NairTenenbaum/Contributions/ThirdContribution.lean) | Large smooth-divisor predicate and sieve-level bound |
| [ThirdContributionWeights](NairTenenbaum/Contributions/ThirdContributionWeights.lean) | The weighted sum over values with a large smooth radical divisor |
| [ValueBoundContributions](NairTenenbaum/Contributions/ValueBoundContributions.lean) | All four majorants under a direct bound on polynomial values |

</details>

<details>
<summary>PrimeArguments (25 modules)</summary>

| Module | Content |
| --- | --- |
| [PrimeArgumentBadSieve](NairTenenbaum/PrimeArguments/PrimeArgumentBadSieve.lean) | Full bad-prime summation for the prime-argument sieve |
| [PrimeArgumentBand](NairTenenbaum/PrimeArguments/PrimeArgumentBand.lean) | A logarithmic prime band with the additional prime-argument saving |
| [PrimeArgumentBandContribution](NairTenenbaum/PrimeArguments/PrimeArgumentBandContribution.lean) | The weighted contribution of a smooth prefix at prime arguments |
| [PrimeArgumentBands](NairTenenbaum/PrimeArguments/PrimeArgumentBands.lean) | Summing logarithmic prefix bands at prime arguments |
| [PrimeArgumentCover](NairTenenbaum/PrimeArguments/PrimeArgumentCover.lean) | Covering the fourth class at prime arguments by logarithmic bands |
| [PrimeArgumentDecomposition](NairTenenbaum/PrimeArguments/PrimeArgumentDecomposition.lean) | The four contribution classes restricted to prime arguments |
| [PrimeArgumentEuler](NairTenenbaum/PrimeArguments/PrimeArgumentEuler.lean) | The extra logarithm in the prime-argument Euler product |
| [PrimeArgumentExceptional](NairTenenbaum/PrimeArguments/PrimeArgumentExceptional.lean) | Power savings with the growth margin of Theorem 3 |
| [PrimeArgumentFirstContribution](NairTenenbaum/PrimeArguments/PrimeArgumentFirstContribution.lean) | The small-prefix contribution at prime arguments |
| [PrimeArgumentHeight](NairTenenbaum/PrimeArguments/PrimeArgumentHeight.lean) | Common height and growth margins for Theorems 1 and 3 |
| [PrimeArgumentIntervalBound](NairTenenbaum/PrimeArguments/PrimeArgumentIntervalBound.lean) | The four prime-argument contributions assembled with uniform constants |
| [PrimeArgumentMainTerm](NairTenenbaum/PrimeArguments/PrimeArgumentMainTerm.lean) | The sifted small-divisor sum bounded by the original main term |
| [PrimeArgumentMajorant](NairTenenbaum/PrimeArguments/PrimeArgumentMajorant.lean) | Prime arguments in the selected-prefix majorant |
| [PrimeArgumentMoment](NairTenenbaum/PrimeArguments/PrimeArgumentMoment.lean) | Smooth moments with the additional prime-argument totient power |
| [PrimeArgumentRoots](NairTenenbaum/PrimeArguments/PrimeArgumentRoots.lean) | Adjoining the prime argument to the sieve polynomial |
| [PrimeArgumentScales](NairTenenbaum/PrimeArguments/PrimeArgumentScales.lean) | Sieve levels for prime arguments with the original degree and growth exponent |
| [PrimeArgumentSieve](NairTenenbaum/PrimeArguments/PrimeArgumentSieve.lean) | The conditional sieve for prime arguments |
| [PrimeArgumentSieveLevel](NairTenenbaum/PrimeArguments/PrimeArgumentSieveLevel.lean) | Absorbing the prime-argument sieve remainder |
| [PrimeArgumentSmallSieve](NairTenenbaum/PrimeArguments/PrimeArgumentSmallSieve.lean) | Summing the prime-argument sieve over the small good tuples |
| [PrimeArgumentSmallSum](NairTenenbaum/PrimeArguments/PrimeArgumentSmallSum.lean) | The prime-argument sieve in the original divisor tuple variables |
| [PrimeArgumentSplitTail](NairTenenbaum/PrimeArguments/PrimeArgumentSplitTail.lean) | Prime-argument smooth tails retaining the full bad-prime mass |
| [PrimeArgumentTailMajorant](NairTenenbaum/PrimeArguments/PrimeArgumentTailMajorant.lean) | Selected smooth prefixes at prime arguments with a lower mass cutoff |
| [PrimeArgumentTailReindex](NairTenenbaum/PrimeArguments/PrimeArgumentTailReindex.lean) | Reindexing the smooth prefix tail for prime arguments |
| [PrimeArgumentTailSieve](NairTenenbaum/PrimeArguments/PrimeArgumentTailSieve.lean) | The conditional sieve on a smooth mass tail |
| [PrimeShortSum](NairTenenbaum/PrimeArguments/PrimeShortSum.lean) | The sum over prime arguments in a real interval |

</details>

<details>
<summary>Progressions (11 modules)</summary>

| Module | Content |
| --- | --- |
| [AffineBadDiscriminant](NairTenenbaum/Progressions/AffineBadDiscriminant.lean) | Transformed restricted discriminant divides the original one |
| [AffineDiscriminant](NairTenenbaum/Progressions/AffineDiscriminant.lean) | Exact resultant and discriminant scaling under affine substitution |
| [AffineIntervalRange](NairTenenbaum/Progressions/AffineIntervalRange.lean) | Uniform interval ranges under finitely many affine substitutions |
| [AffineIrreducibility](NairTenenbaum/Progressions/AffineIrreducibility.lean) | Irreducibility survives the affine primitive-part reduction |
| [AffineNoFixedPrime](NairTenenbaum/Progressions/AffineNoFixedPrime.lean) | Removing fixed prime divisors on finitely many progressions |
| [AffinePolynomialContent](NairTenenbaum/Progressions/AffinePolynomialContent.lean) | Content after restriction to an arithmetic progression |
| [AffinePolynomialSystem](NairTenenbaum/Progressions/AffinePolynomialSystem.lean) | Construction of the substituted system, preserving irreducibility, nonassociation, and total degree |
| [AffineRootCounts](NairTenenbaum/Progressions/AffineRootCounts.lean) | Root counts and omitted-prime Euler product after arithmetic-progression substitution |
| [AffineWeights](NairTenenbaum/Progressions/AffineWeights.lean) | Exact weight identity with the progression coprimality restriction |
| [ProgressionBound](NairTenenbaum/Progressions/ProgressionBound.lean) | Progression estimate at the original scale, with a height threshold independent of β |
| [ProgressionIntervals](NairTenenbaum/Progressions/ProgressionIntervals.lean) | Progression reindexing and exact main-term identity |

</details>

<details>
<summary>Hooley (40 modules)</summary>

| Module | Content |
| --- | --- |
| [Hooley](NairTenenbaum/Hooley/Hooley.lean) | `Δ`, attainment of its maximum, coprime divisor-window identity, `Δ(mn) ≤ τ(m)Δ(n)`, and the pointwise dyadic divisor bound |
| [HooleyAffineReduction](NairTenenbaum/Hooley/HooleyAffineReduction.lean) | Reducing Hooley short sums to primitive affine restrictions |
| [HooleyAverageReductions](NairTenenbaum/Hooley/HooleyAverageReductions.lean) | Corollaries 5 and 9 reduced to the same reciprocal Hooley mean, uniformly in the dyadic cutoff |
| [HooleyCoarseLogBound](NairTenenbaum/Hooley/HooleyCoarseLogBound.lean) | Absorbing the subexponential factor into a logarithmic margin |
| [HooleyDifferentialInequality](NairTenenbaum/Hooley/HooleyDifferentialInequality.lean) | Unconditional differential inequality with explicit prime and divisor series |
| [HooleyDirichletCoefficients](NairTenenbaum/Hooley/HooleyDirichletCoefficients.lean) | Squarefree moment coefficients and subpolynomial bounds uniform in moment order |
| [HooleyDirichletDerivative](NairTenenbaum/Hooley/HooleyDirichletDerivative.lean) | Termwise differentiation with a proved summable majorant |
| [HooleyDirichletError](NairTenenbaum/Hooley/HooleyDirichletError.lean) | Summable mixed error with nonlinear interpolation between divisor and moment series |
| [HooleyDirichletPowerBound](NairTenenbaum/Hooley/HooleyDirichletPowerBound.lean) | Uniform bound `(Kq)^q (σ−1)^(−(2^t−t+t/q))` |
| [HooleyDirichletPrimeExpansion](NairTenenbaum/Hooley/HooleyDirichletPrimeExpansion.lean) | Exact prime expansion of the Dirichlet derivative with squarefree and coprimality conditions |
| [HooleyDirichletSeries](NairTenenbaum/Hooley/HooleyDirichletSeries.lean) | Convergence of the moment Dirichlet series and its logarithmic companion for `σ>1` |
| [HooleyDivisorEulerBound](NairTenenbaum/Hooley/HooleyDivisorEulerBound.lean) | Divisor Dirichlet series bounded by the exponential of `2^t` times the prime root series |
| [HooleyDivisorTail](NairTenenbaum/Hooley/HooleyDivisorTail.lean) | A uniform negligible tail for large divisor-window counts |
| [HooleyExponentGap](NairTenenbaum/Hooley/HooleyExponentGap.lean) | Positive exponent gap with lower bound `t/(7q(q−1))` for `t≥1` and `q≥2t` |
| [HooleyFixedFactor](NairTenenbaum/Hooley/HooleyFixedFactor.lean) | Absorbing a fixed factor in Hooley's function |
| [HooleyFixedPrimeBound](NairTenenbaum/Hooley/HooleyFixedPrimeBound.lean) | Hooley moments without the no-fixed-prime-divisor restriction |
| [HooleyFixedPrimeTail](NairTenenbaum/Hooley/HooleyFixedPrimeTail.lean) | Divisor-window tail saving in the presence of fixed prime divisors |
| [HooleyInfinitePrimeStep](NairTenenbaum/Hooley/HooleyInfinitePrimeStep.lean) | Convergence of the root-weighted prime series and the infinite fractional-moment prime step |
| [HooleyIntegratedBound](NairTenenbaum/Hooley/HooleyIntegratedBound.lean) | Unconditional endpoint-plus-integral bound for the transformed moment series |
| [HooleyIntegratedPowerBound](NairTenenbaum/Hooley/HooleyIntegratedPowerBound.lean) | Integrated power estimate retaining the exact exponent-gap dependence |
| [HooleyIntegratingFactor](NairTenenbaum/Hooley/HooleyIntegratingFactor.lean) | Transformed derivative bounded using only prime series and explicit constants |
| [HooleyLogarithmicSaving](NairTenenbaum/Hooley/HooleyLogarithmicSaving.lean) | Choosing a Hooley moment that gives logarithmic tail saving |
| [HooleyMomentComparison](NairTenenbaum/Hooley/HooleyMomentComparison.lean) | Maximum-to-moment comparison with factor `2^(q-1)` and positivity |
| [HooleyMomentInterpolation](NairTenenbaum/Hooley/HooleyMomentInterpolation.lean) | Interpolation between the first and higher moments, including mixed products |
| [HooleyMomentOrderConstants](NairTenenbaum/Hooley/HooleyMomentOrderConstants.lean) | Integrated coefficient bounded linearly in the moment order |
| [HooleyMomentRecovery](NairTenenbaum/Hooley/HooleyMomentRecovery.lean) | Recovery of the original series with exponent `2^t−t+t/q` |
| [HooleyMomentRecurrence](NairTenenbaum/Hooley/HooleyMomentRecurrence.lean) | Exact coprime prime recurrence and mixed moments |
| [HooleyMoments](NairTenenbaum/Hooley/HooleyMoments.lean) | Integral moments, window measurability and integrability, and the divisor-count upper bound |
| [HooleyPowerMajorant](NairTenenbaum/Hooley/HooleyPowerMajorant.lean) | Explicit power majorant with constants chosen uniformly in moment order |
| [HooleyPowerfulComparison](NairTenenbaum/Hooley/HooleyPowerfulComparison.lean) | Unrestricted Hooley mean bounded by its squarefree counterpart |
| [HooleyPrimeMixedBound](NairTenenbaum/Hooley/HooleyPrimeMixedBound.lean) | Prime-summed mixed-moment bound with explicit `4^q` dependence |
| [HooleyPrimeSampling](NairTenenbaum/Hooley/HooleyPrimeSampling.lean) | Finite weighted sampling bound for translated divisor windows |
| [HooleyPrimeShortSum](NairTenenbaum/Hooley/HooleyPrimeShortSum.lean) | Shifted-prime Hooley moments, including the uniform range `1≤\|a\|≤x` |
| [HooleyShortSum](NairTenenbaum/Hooley/HooleyShortSum.lean) | Polynomial Hooley moments reduced to root-weighted means for every positive interval exponent |
| [HooleySquarefreeMean](NairTenenbaum/Hooley/HooleySquarefreeMean.lean) | Sharp reciprocal Hooley mean over squarefree integers |
| [HooleySquarefreePowerBound](NairTenenbaum/Hooley/HooleySquarefreePowerBound.lean) | Logarithmic finite-sum bound with moment-independent cutoff |
| [HooleySquarefreeRankin](NairTenenbaum/Hooley/HooleySquarefreeRankin.lean) | Finite squarefree reciprocal sums bounded by moment Dirichlet series |
| [HooleyTotientMean](NairTenenbaum/Hooley/HooleyTotientMean.lean) | Sharp Hooley mean with a uniform reciprocal-totient factor |
| [HooleyWeightedMean](NairTenenbaum/Hooley/HooleyWeightedMean.lean) | Sharp unrestricted reciprocal Hooley mean with coefficient sqrt(2t) |
| [HooleyWeightedPrimeStep](NairTenenbaum/Hooley/HooleyWeightedPrimeStep.lean) | Root-weighted finite prime recurrence with an explicit mixed error |

</details>

<details>
<summary>DivisorSums (11 modules)</summary>

| Module | Content |
| --- | --- |
| [DivisorHitFixedPrime](NairTenenbaum/DivisorSums/DivisorHitFixedPrime.lean) | Divisor hits without a restriction on fixed prime divisors |
| [DivisorWindowMoments](NairTenenbaum/DivisorSums/DivisorWindowMoments.lean) | Divisor windows and moment truncation for Theorem 2 |
| [GoldbachScales](NairTenenbaum/DivisorSums/GoldbachScales.lean) | Uniform cutoff choice and logarithm-squared bound for lengths at least `N^θ` |
| [GoldbachSieve](NairTenenbaum/DivisorSums/GoldbachSieve.lean) | Two-prime sieve with explicit reciprocal-totient correction and separate small-prime exceptions |
| [GreatestPrimeFactorCount](NairTenenbaum/DivisorSums/GreatestPrimeFactorCount.lean) | Greatest prime factors and divisor hits |
| [GreatestPrimeFactorExponent](NairTenenbaum/DivisorSums/GreatestPrimeFactorExponent.lean) | The exponent margin in Theorem 2 |
| [PolynomialDivisorWindowCount](NairTenenbaum/DivisorSums/PolynomialDivisorWindowCount.lean) | Double counting polynomial divisors in a dyadic window |
| [PrimeFactorLogGain](NairTenenbaum/DivisorSums/PrimeFactorLogGain.lean) | Quantitative logarithmic gain from saved prime factors |
| [RoughCofactorBounds](NairTenenbaum/DivisorSums/RoughCofactorBounds.lean) | Prime-factor counts of the rough cofactor in Theorem 2 |
| [RoughLogMass](NairTenenbaum/DivisorSums/RoughLogMass.lean) | Counting a saved prime factor in the total rough logarithmic mass |
| [ScalarRoughLogMass](NairTenenbaum/DivisorSums/ScalarRoughLogMass.lean) | Logarithmic mass of the canonical rough parts |

</details>

<details>
<summary>NumberFields (52 modules)</summary>

| Module | Content |
| --- | --- |
| [ArithmeticLogDerivative](NairTenenbaum/NumberFields/ArithmeticLogDerivative.lean) | Logarithmic derivation, ideal von Mangoldt function, and exact convolution identity |
| [ArithmeticLogDerivativeSupport](NairTenenbaum/NumberFields/ArithmeticLogDerivativeSupport.lean) | Prime-power support via multiplicativity in the square-zero extension |
| [ConductorNonzero](NairTenenbaum/NumberFields/ConductorNonzero.lean) | Discriminant argument proving the conductor exponent is nonzero |
| [ConductorQuotient](NairTenenbaum/NumberFields/ConductorQuotient.lean) | Polynomial quotient description for every modulus coprime to the conductor exponent |
| [ConvolutionMean](NairTenenbaum/NumberFields/ConvolutionMean.lean) | Exact convolution summatory identity and transfer of linear means under absolute summability |
| [ConvolutionPowerError](NairTenenbaum/NumberFields/ConvolutionPowerError.lean) | Linear convolution error from a power-saving summatory estimate |
| [DirichletInverseGrowth](NairTenenbaum/NumberFields/DirichletInverseGrowth.lean) | Uniform exponential bounds for local inverse and convolution coefficients |
| [EulerSummabilityCriterion](NairTenenbaum/NumberFields/EulerSummabilityCriterion.lean) | Global convergence of a multiplicative function from summable local tails |
| [GeometricEulerDerivative](NairTenenbaum/NumberFields/GeometricEulerDerivative.lean) | Explicit logarithmic derivatives of weighted geometric series |
| [IdealClassPowerError](NairTenenbaum/NumberFields/IdealClassPowerError.lean) | Power-saving counts in every ideal class, including torsion multiplicity and norm scaling |
| [IdealFiniteEulerBound](NairTenenbaum/NumberFields/IdealFiniteEulerBound.lean) | Ideal-factorization injection and geometric Euler bound |
| [IdealLocalEulerPolynomial](NairTenenbaum/NumberFields/IdealLocalEulerPolynomial.lean) | Polynomial inverse of the local ideal-counting series at every prime |
| [IdealMangoldtMertensReduction](NairTenenbaum/NumberFields/IdealMangoldtMertensReduction.lean) | Conditional sharp Mertens bound from quantitative ideal counting |
| [IdealMultiplicityVectors](NairTenenbaum/NumberFields/IdealMultiplicityVectors.lean) | Exact bijection between ideals of prime-power norm and weighted multiplicity vectors |
| [IdealNormDirichlet](NairTenenbaum/NumberFields/IdealNormDirichlet.lean) | Convergent real ideal-norm series, Dedekind zeta identity, and simple-pole bound |
| [IdealNormMean](NairTenenbaum/NumberFields/IdealNormMean.lean) | Multiplicative ideal-count arithmetic function, its positive mean, and convolution mean formula |
| [IdealNormMultiplicative](NairTenenbaum/NumberFields/IdealNormMultiplicative.lean) | Unique factorization into ideals of specified coprime norms and multiplicativity of their counts |
| [IdealNormPowerError](NairTenenbaum/NumberFields/IdealNormPowerError.lean) | Quantitative ideal count with the Dedekind zeta residue as leading coefficient |
| [IdealPrimePowerCountBound](NairTenenbaum/NumberFields/IdealPrimePowerCountBound.lean) | Ideal counts of norm `p^k` bounded by `(k+1)^[K:ℚ]` |
| [IdealRootEulerBound](NairTenenbaum/NumberFields/IdealRootEulerBound.lean) | Full ideal-norm series bounded above by the root Euler exponential |
| [IdealVonMangoldtBounds](NairTenenbaum/NumberFields/IdealVonMangoldtBounds.lean) | Nonnegativity, pointwise comparison, and linear Chebyshev bound |
| [IdealVonMangoldtLocal](NairTenenbaum/NumberFields/IdealVonMangoldtLocal.lean) | Exact local von Mangoldt formula and prime-power degree bound |
| [IntegralRootNormalization](NairTenenbaum/NumberFields/IntegralRootNormalization.lean) | Integral primitive generator and residue-root comparison for a general integer polynomial |
| [IrreduciblePrimeIdealMatch](NairTenenbaum/NumberFields/IrreduciblePrimeIdealMatch.lean) | Eventual equality of original polynomial roots and prime-norm ideal counts |
| [IrreduciblePrimeLogBound](NairTenenbaum/NumberFields/IrreduciblePrimeLogBound.lean) | Sharp prime-root logarithmic bound for every integer polynomial irreducible over ℚ |
| [IrreduciblePrimeLowerBound](NairTenenbaum/NumberFields/IrreduciblePrimeLowerBound.lean) | Sharp lower logarithmic bound for irreducible-polynomial prime-root series |
| [IrreducibleRootDensity](NairTenenbaum/NumberFields/IrreducibleRootDensity.lean) | Positive mean and dyadic root-density lower bound for original irreducible polynomials |
| [IrreducibleSieveProduct](NairTenenbaum/NumberFields/IrreducibleSieveProduct.lean) | Irreducible-polynomial sieve product bounded by a constant divided by log x |
| [LogWeightedSummatoryBound](NairTenenbaum/NumberFields/LogWeightedSummatoryBound.lean) | Logarithmic weighting with a linear error under a power-saving mean estimate |
| [MinpolyEulerProduct](NairTenenbaum/NumberFields/MinpolyEulerProduct.lean) | Good-prime root Euler product bounded by the ideal-norm series |
| [MinpolyPrimeLogBound](NairTenenbaum/NumberFields/MinpolyPrimeLogBound.lean) | Sharp logarithmic bound for the prime root series of an integral primitive generator |
| [MinpolyPrimeLowerBound](NairTenenbaum/NumberFields/MinpolyPrimeLowerBound.lean) | Sharp lower logarithmic bound for the minimal-polynomial prime-root series |
| [NumberFieldPrimeNormRoots](NairTenenbaum/NumberFields/NumberFieldPrimeNormRoots.lean) | Exact equality of good-prime residue-root counts and prime-norm ideal counts |
| [NumberFieldResidueRoots](NairTenenbaum/NumberFields/NumberFieldResidueRoots.lean) | Injective construction of ideals from minimal-polynomial residue roots |
| [PowerErrorMean](NairTenenbaum/NumberFields/PowerErrorMean.lean) | Identification of a power-saving count’s leading coefficient from its qualitative mean |
| [PowerSeriesEulerDerivative](NairTenenbaum/NumberFields/PowerSeriesEulerDerivative.lean) | Euler differentiation of formal power series and finite inverse products |
| [PrimeIdealErrorBounds](NairTenenbaum/NumberFields/PrimeIdealErrorBounds.lean) | Convergent quadratic errors from prime ideals of higher residue degree |
| [PrimeIdealNormBounds](NairTenenbaum/NumberFields/PrimeIdealNormBounds.lean) | Prime-ideal norms and the degree bound on primes above a rational prime |
| [PrimeIdealResidueDegree](NairTenenbaum/NumberFields/PrimeIdealResidueDegree.lean) | Residue-degree sum bound and exact description of prime-norm ideals |
| [PrimeIdealRootComparison](NairTenenbaum/NumberFields/PrimeIdealRootComparison.lean) | Degree-one prime ideals compared with polynomial residue roots |
| [PrimeIdealSupport](NairTenenbaum/NumberFields/PrimeIdealSupport.lean) | Canonical finite support of prime ideals above a rational prime |
| [PrimeRootMangoldtBound](NairTenenbaum/NumberFields/PrimeRootMangoldtBound.lean) | Weighted prime-root sum bounded by the ideal reciprocal sum plus a fixed constant |
| [PrimeRootMertens](NairTenenbaum/NumberFields/PrimeRootMertens.lean) | Unconditional sharp weighted prime-root bound log(x)+O(1) |
| [PrimeRootReciprocalLowerBound](NairTenenbaum/NumberFields/PrimeRootReciprocalLowerBound.lean) | Truncated prime-root reciprocal sum bounded below by log log x minus a constant |
| [ResidueHomKernels](NairTenenbaum/NumberFields/ResidueHomKernels.lean) | Residue homomorphisms are determined by their kernels, with exact quotient cardinality |
| [RootDensityFromIdealCounts](NairTenenbaum/NumberFields/RootDensityFromIdealCounts.lean) | Positive root mean from eventual agreement with prime-norm ideal counts |
| [RootIdealCorrection](NairTenenbaum/NumberFields/RootIdealCorrection.lean) | Exact squarefree-root/ideal convolution correction and cancellation of its good-prime coefficients |
| [RootIdealCorrectionGrowth](NairTenenbaum/NumberFields/RootIdealCorrectionGrowth.lean) | Explicit exponential coefficient bound for the correction of a primitive polynomial |
| [RootIdealCorrectionPositive](NairTenenbaum/NumberFields/RootIdealCorrectionPositive.lean) | Positivity of the global correction assuming absolute convergence |
| [RootIdealCorrectionTail](NairTenenbaum/NumberFields/RootIdealCorrectionTail.lean) | Summable `O(1/p²)` positive-exponent tails at sufficiently large good primes |
| [RootIdealLocalPolynomial](NairTenenbaum/NumberFields/RootIdealLocalPolynomial.lean) | Finite local correction with absolute summability and positive value at `1/p` |
| [RootNormalizationEquality](NairTenenbaum/NumberFields/RootNormalizationEquality.lean) | Exact residue-root equality under integral normalization at good primes |

</details>

<details>
<summary>Geometry (13 modules)</summary>

| Module | Content |
| --- | --- |
| [CubeFaces](NairTenenbaum/Geometry/CubeFaces.lean) | Smooth lower-dimensional parametrizations of coordinate cube faces |
| [IntegerLatticeBallBound](NairTenenbaum/Geometry/IntegerLatticeBallBound.lean) | Uniform integer lattice-point bounds in balls and finite ball covers |
| [IntegerLatticeBoundary](NairTenenbaum/Geometry/IntegerLatticeBoundary.lean) | Every bounded region has lattice discrepancy bounded by mixed boundary cells |
| [IntegerLatticeCells](NairTenenbaum/Geometry/IntegerLatticeCells.lean) | Unit-cell partition, exact volumes, and a finite cell-sandwich discrepancy bound |
| [LatticeCoordinateCount](NairTenenbaum/Geometry/LatticeCoordinateCount.lean) | Exact conversion of arbitrary integral-basis lattice counts to integer coordinates |
| [LatticePointsNearChart](NairTenenbaum/Geometry/LatticePointsNearChart.lean) | A fixed neighborhood of a dilated m-parameter chart contains O(t^m) lattice points |
| [LipschitzBoundaryLatticeCount](NairTenenbaum/Geometry/LipschitzBoundaryLatticeCount.lean) | Quantitative lattice discrepancy for finitely many Lipschitz boundary charts |
| [LipschitzCubeCover](NairTenenbaum/Geometry/LipschitzCubeCover.lean) | Explicit mesh covers and covering cardinalities for dilated Lipschitz cube images |
| [MixedPolarCoordinates](NairTenenbaum/Geometry/MixedPolarCoordinates.lean) | Signs and compact angular coordinates in mixed embedding space |
| [NormConeLatticePowerError](NairTenenbaum/Geometry/NormConeLatticePowerError.lean) | Power-saving fundamental-cone lattice count with exponent (degree-1)/degree |
| [NormLeOneBoundaryCharts](NairTenenbaum/Geometry/NormLeOneBoundaryCharts.lean) | Finite smooth boundary charts and quantitative lattice count for the norm-one region |
| [NormLeOneBoundaryRadii](NairTenenbaum/Geometry/NormLeOneBoundaryRadii.lean) | Radial and unit-coordinate endpoint description of the norm-one boundary |
| [NormLeOneRadialCharts](NairTenenbaum/Geometry/NormLeOneRadialCharts.lean) | Smooth full-dimensional charts and their boundary-face representation |

</details>

<details>
<summary>Results (23 modules)</summary>

| Module | Content |
| --- | --- |
| [CorollaryEight](NairTenenbaum/Results/CorollaryEight.lean) | Corollary 8 with both inequalities uniform in nonzero shifts up to x |
| [CorollaryFive](NairTenenbaum/Results/CorollaryFive.lean) | Corollary 5 with constants uniform in the dyadic cutoff |
| [CorollaryFour](NairTenenbaum/Results/CorollaryFour.lean) | Corollary 4 for every moment order at least one and every positive interval exponent |
| [CorollaryNine](NairTenenbaum/Results/CorollaryNine.lean) | Corollary 9 uniform in the dyadic cutoff and nonzero residues up to x |
| [CorollaryOne](NairTenenbaum/Results/CorollaryOne.lean) | Proposition `CorollaryOne` and proof `corollaryOne` |
| [CorollarySeven](NairTenenbaum/Results/CorollarySeven.lean) | Shifted-prime estimate with both constants uniform in the nonzero shift |
| [CorollarySix](NairTenenbaum/Results/CorollarySix.lean) | Exponential smoothness saving for a nonconstant restricted coordinate |
| [CorollaryTen](NairTenenbaum/Results/CorollaryTen.lean) | Goldbach bound with one prime in `(x,x+y]` under the original hypotheses |
| [CorollaryThree](NairTenenbaum/Results/CorollaryThree.lean) | Corollary 3 with uniform constants in the factorization interface |
| [CorollaryTwo](NairTenenbaum/Results/CorollaryTwo.lean) | Equation (20), with factorization data constructed from the polynomial hypotheses |
| [FamilyTheorems](NairTenenbaum/Results/FamilyTheorems.lean) | Theorem 1 and Corollaries 1 and 3 for original polynomials, with no factorization-data hypothesis |
| [LemmaTwo](NairTenenbaum/Results/LemmaTwo.lean) | Full Lemma 2 with class-`M` weights and Theorem 1 parameters, including cutoffs below two |
| [PrimeFamilyTheorem](NairTenenbaum/Results/PrimeFamilyTheorem.lean) | Theorem 3 for original polynomial families, with constructed factorization data |
| [SmoothFamilyTheorem](NairTenenbaum/Results/SmoothFamilyTheorem.lean) | Corollary 6 for original polynomial families, with factorization constructed |
| [Targets](NairTenenbaum/Results/Targets.lean) | Proposition `TheoremOne`, with uniform constants quantified before the polynomial family and function |
| [TheoremOne](NairTenenbaum/Results/TheoremOne.lean) | Proof `theoremOne : TheoremOne` and a bound uniform in the numbers of polynomials and factors at fixed degree |
| [TheoremThree](NairTenenbaum/Results/TheoremThree.lean) | Theorem 3 with its original growth and interval hypotheses and explicit constant-term correction |
| [TheoremTwo](NairTenenbaum/Results/TheoremTwo.lean) | Full Theorem 2 under the original irreducible-polynomial hypotheses |
| [TheoremTwoDivisorHits](NairTenenbaum/Results/TheoremTwoDivisorHits.lean) | Divisor hits in the interval prescribed by Theorem 2 |
| [TheoremTwoLogGain](NairTenenbaum/Results/TheoremTwoLogGain.lean) | Linear-error absorption and the strict exponent margin |
| [TheoremTwoRoughMass](NairTenenbaum/Results/TheoremTwoRoughMass.lean) | Rough logarithmic mass with a linear error and exact interval cardinality |
| [TheoremTwoStatement](NairTenenbaum/Results/TheoremTwoStatement.lean) | Statement of Theorem 2 |
| [TheoremTwoValueBounds](NairTenenbaum/Results/TheoremTwoValueBounds.lean) | Fixed polynomial-value and prime-cutoff constants for Theorem 2 |

</details>

<details>
<summary>Counterexamples (5 modules)</summary>

| Module | Content |
| --- | --- |
| [ConstantCoordinate](NairTenenbaum/Counterexamples/ConstantCoordinate.lean) | The family `(X,1)`, its exact smooth sum, and an upper bound for its main term |
| [CorollarySixObstruction](NairTenenbaum/Counterexamples/CorollarySixObstruction.lean) | Counterexample to dropping nonconstancy of the restricted polynomial |
| [LemmaOneCounterexample](NairTenenbaum/Counterexamples/LemmaOneCounterexample.lean) | Full arithmetic counterexample to the printed comparison in Lemma 1, including (23) and the weights for `Q=X` |
| [LemmaOneObstruction](NairTenenbaum/Counterexamples/LemmaOneObstruction.lean) | Failure of the local summability deduction used in Lemma 1 |
| [PrimeSupportedFunction](NairTenenbaum/Counterexamples/PrimeSupportedFunction.lean) | Admissible functions supported on powers of two and completely multiplicative twists |

</details>
