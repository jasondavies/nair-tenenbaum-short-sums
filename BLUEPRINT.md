# Proof map and source corrections

Reference: Nair–Tenenbaum, *Short sums of certain arithmetic functions*, Acta Math.
180 (1998), 119–144. Equation and section numbers refer to the
[author's PDF](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf).

All numbered results have proofs or the explicit corrections and counterexamples
recorded below. The general class-`M` version of Lemma 2 is proved as
`lemmaTwo : LemmaTwo`. Theorem 1 is proved as
`NairTenenbaum.theoremOne : NairTenenbaum.TheoremOne`, and Corollary 1 as
`NairTenenbaum.corollaryOne : NairTenenbaum.CorollaryOne`. Corollary 2 is proved as
`NairTenenbaum.corollaryTwo : NairTenenbaum.CorollaryTwo`, with its factorization
data constructed from the original irreducible family. Corollary 3 is proved as
`NairTenenbaum.corollaryThree : NairTenenbaum.CorollaryThree`. Theorem 3 and
Corollary 7 are proved as `theoremThree : TheoremThree` and
`corollarySeven : CorollarySeven`. Corollary 10 is proved as
`corollaryTen : CorollaryTen`. Corollary 6 is proved as `corollarySix : CorollarySix`
with an explicit nonconstancy condition on the restricted coordinate;
`CorollarySixObstruction` proves this condition is necessary in the general
family interface. Corollaries 5, 8, and 9 are proved as `corollaryFive`,
`corollaryEight`, and `corollaryNine`; the latter two retain the uniform
nonzero shift/residue range `|a|≤x`. Corollary 4 is proved as `corollaryFour : CorollaryFour`. Theorem 2 is proved as `theoremTwo : TheoremTwo`.
`FamilyFactorization` constructs the common
irreducible factor data for arbitrary admissible integer polynomial families.
`FamilyTheorems` provides `theoremOne_for_families`, `corollaryOne_for_families`,
and `corollaryThree_for_families`, removing the separate factorization-data
hypothesis from the user-facing statements.

## Arithmetic foundation

| Paper item | Lean declaration | Status |
|---|---|---|
| (1), definition of `𝓜ₖ(A,B,ε)` | `Admissible`, `growthBound` | Defined |
| `Ω(mn)=Ω(m)+Ω(n)` | `bigOmega_mul` | Proved for nonzero factors |
| Vanishing if `F(1)=0` | `Admissible.eq_zero_of_one` | Proved |
| Scaling and positive powers | `Admissible.smul`, `Admissible.rpow` | Proved |
| (11), minimal majorant | `minimalMajorant`, `majorantRatios` | Defined using `sSup` |
| (12) | `Admissible.le_minimalMajorant_mul` | Proved, including zero denominators |
| (13) | `Admissible.minimalMajorant_le` | Proved |
| Submultiplicativity following (13) | `Admissible.minimalMajorant_submultiplicative` | Proved |
| `G_F ∈ 𝓜ₖ(A,B,ε)` | `Admissible.minimalMajorant_admissible` | Proved |
| (14) | `Admissible.minimalMajorant_le_primeMajorant` | Proved in all dimensions |
| (15) and the identities for `n'`, `n''` | `pullback`, `substitute_mul`, `mass_substitute`, `weightedMass_mul` | Defined/proved |
| (16) | `weight`, `Dagger`, `mem_weightFiber` | Defined; finiteness justified |
| Irreducible-coordinate specialization | `substitute_identity`, `weightedMass_identity` | Proved |
| One-variable weight | `weight_one_variable` | Proved with the discriminant condition retained |
| Multiplicative auxiliary functions `f_h` | `auxiliary`, `auxiliary_mul`, `auxiliary_prime_pow` | Defined and proved multiplicative |
| (17) | `Admissible.pullback_minimalMajorant_le_auxiliary` | Proved for arbitrary positive tuples |
| Local geometric bounds and convergence | `auxiliaryLocal_le_geometric`, `auxiliaryLocal_summable`, `auxiliaryLocal_tail_le` | Proved |
| Finite smooth Euler product | `auxiliary_smooth_hasSum` | Proved; no global summability assumption |
| Prime-support splitting, (28)–(30) | `primeSelect_mul_primeReject`, `primeSelect_primeReject_coprime`, `Admissible.pullback_primeSplit_le`, `Admissible.pullback_minimalMajorant_le_growth` | Proved |

`substitute_coprime` deliberately requires cross-coordinate coprimality of the two
input tuples: coordinatewise coprimality before substitution alone does not imply
coordinatewise coprimality after mixing coordinates with an exponent matrix.

## Polynomial and sieve data

`PolynomialSystem` encodes the factorization (9), rational irreducibility,
nonassociation, positive total exponents, unit signs and absence of a fixed prime
divisor. `PolynomialSystem.abs_eval_factorization` proves the corresponding
absolute-value identity. `PolynomialSystem.badDiscriminant` implements the
restricted discriminant factor `D` from §2, rather than the full discriminant.
`PolynomialStructure` proves `g = ∑ γ_h deg R_h`, bounds the number of factors
by `g`, proves separability of the radical over the rationals, and deduces that
its discriminant is nonzero from the resultant identity.

`rootCount_mul` is proved by constructing `rootsCRT`, an equivalence between
roots modulo coprime products and pairs of roots. The prime root bound and the
root-count identity for products of positive powers are also proved.
`PolynomialSystem.rootCount_total_eq_radical` includes the unit signs in the
factorization; each irreducible factor inherits the no-fixed-prime-divisor condition.

`PrimePowerRoots` proves `ρ_Q(p^ν) ≤ ρ_Q(p)` for `ν > 0` when all roots modulo
`p` are simple, in particular when the reduction is separable. It uses uniqueness
of a simple root in the local ring `ZMod (p^ν)`.

`DiscriminantBezout` constructs the discriminant as `Q U + Q' V` in degree at
least two using the adjugate of the modified Sylvester matrix. This proves
simplicity at primes not dividing the discriminant without an extra condition
on the leading coefficient. Degrees zero and one are handled separately using
the no-fixed-prime hypothesis.

`PolynomialLocal.factor_rootCount_prime_pow_le_of_not_dvd_bad` proves
`ρ_h(p^ν) ≤ ρ_h(p)` for every `ν > 0` and `p ∤ D`, using the exact prime support
of the restricted bad discriminant. `common_value_gcd_dvd_discriminant` proves
that `gcd(|R_i(n)|, |R_j(n)|)` divides `|D*|` when `i ≠ j`.

`BadPrimeRoots.root_difference_dvd_of_discr` uses Taylor expansion and the
discriminant identity to show that roots modulo `p^ν` agreeing modulo `p^(δ+1)`
agree modulo `p^(ν-δ)`, whenever `p^(δ+1)` does not divide the discriminant.
An explicit injection recording a low residue and a high quotient then gives
`ρ_Q(p^ν) ≤ p^(2δ+1)`. For the irreducible factors, the exact factorization of
`D` gives `ρ_h(p^ν) ≤ D³` at primes dividing `D`. Thus
`factor_rootCount_prime_pow_uniform` proves the all-prime bound
`ρ_h(p^ν) ≤ max(deg R_h,D³)`, including exponent zero.

`RootAuxiliary` proves multiplicativity, local summability, and the finite Euler
product for `f_h(n)ρ_h(n)/n`. The specialization to a `PolynomialSystem` has no
unproved root-count assumptions. The root-weighted summand for `F` is bounded
pointwise using (12) and (17).

`eval_natAbs_le_height` proves
`|Q(n)| ≤ height(Q) (deg Q + 1) max(1, |n|)^(deg Q)` for integer arguments.

`polynomialCongruenceCount_error` proves the interval distribution estimate
`|#{a<n≤b : q∣Q(n)} - (b-a)ρ_Q(q)/q| ≤ ρ_Q(q)` for arbitrary integer endpoints
`a≤b` and every positive modulus. It sums the exact residue-class counts, using
the floor-function formula from Mathlib. No primality or squarefreeness is assumed.

`linearSystem` is an explicit inhabitant of `PolynomialSystem 1 1`. Its radical
is `X`, both discriminant quantities equal one, and its weight equals `F(n)/n`.

The initial polynomial prerequisites are now complete: `FamilyFactorization`
constructs common irreducible factors and unit signs; the all-prime bounds feed
the second and third contribution estimates; the uniform conditional sieve is
proved; and the coefficient-height bounds are specialized to the §4 scales.

## Hooley's function

`hooleyDelta` uses a supremum of natural-valued logarithmic divisor-window
counts. `hooleyDelta_attained` proves that this supremum is a maximum.
`hooleyDelta_mul_le` proves the coprime multiplication inequality in §1.
`dyadic_divisors_le_delta` proves the pointwise inequality used in Corollary 5;
it is not the asymptotic corollary itself.

`exists_card_divisors_le_rpow` is an elementary proof of the divisor bound. Large
primes use `ν+1 ≤ 2^ν`; the finitely many small primes use Bernoulli's inequality
to absorb `ν+1` into a constant times a geometric progression. The resulting
constant is independent of the integer being factored.

`hooley_admissible` and `hooley_rpow_admissible` prove membership of `Δ` and `Δ^t`
in the arithmetic classes, with arbitrarily small positive growth exponents.
The weighted average estimates quoted from Tenenbaum [9] are not formalized.

## Main proof and applications

### Counterexample to the printed Lemma 1

The displayed hypotheses (23)–(25) control
`∑_{p,ν≥1} |λ(p^ν)| / p^ν`. The proof subsequently inserts `f_h(p^j)` in the
local tails. This deduction is not valid for arbitrary such `λ`.
`LemmaOneObstruction` checks a single-prime example: for `1<a<2`, take
`θ(2^ν)=(2/a)^ν`. The unweighted consecutive differences divided by `2^ν`
are summable, but multiplying by `a^ν` makes every positive-exponent term
equal to `1-a/2`; their partial sums are unbounded. The theorem
`auxiliary_weighted_not_summable` identifies this weight with the actual
`auxiliaryLocal` at `p=2`, `A=2^η`, `B=1`, `γ=1`, for any `0<η<1`.

`LemmaOneObstruction.admissible_counterexample` in `LemmaOneCounterexample` connects this example
to the full arithmetic comparison. Set `a=2^η` with `0<η<1`, let `F(2^ν)=a^ν`
and let `F` vanish elsewhere. `twoSupported_admissible`
proves `F ∈ M₁(a,1,η)`. The positive twist `θ(n)=(2/a)^v₂(n)` is completely
multiplicative on positive integers. Its difference series is summable at every
prime, and the sum over any finite set of primes has one uniform bound.
For `Q=X`, the untwisted weight sum is at most `(1-a/2)⁻¹`, whereas the twisted
sum below `2^N` is at least `N`. Thus every proposed nonnegative comparison
constant fails. `linearSystem_comparison_fails` states this using the actual
polynomial system, discriminant, and root vector. Taking `η` arbitrarily small
also accommodates the paper's small-exponent restrictions.

`ComparisonLocal` proves a sufficient weighted local criterion: if a twist is
constant on positive powers of each prime and `|θ(p)-1| ≤ L/p`, then the actual
local error from the divisor convolution is summable over the primes. Its
bound depends only on the growth parameters and the uniform root-count bound.
The associated finite products of `1 + local error` are uniformly bounded.
`TotientTwist` verifies these stronger hypotheses for `(n/φ(n))^g`, with
`L=2(2^g-1)`, and discharges the root-count assumptions for every polynomial
factor.

`unitary_comparison_sum` in `UnitaryComparison` proves
the finite scalar comparison by expanding the prime-divisor product and
mapping each integer/prime-subset pair injectively to complementary coprime
factors. `ComparisonKernel` sums the resulting kernel using exact finite
Euler products and proves `unitary_comparison_uniform`.
`scalar_totient_comparison_uniform` in `ScalarComparison` instantiates this with
an admissible one-variable function, the polynomial root count, and the dagger
restriction. Its explicit `scalarComparisonBound` depends only on `B`, `ε`,
the totient exponent, and a uniform root-count bound. The theorem
`PolynomialSystem.factor_scalar_totient_comparison` discharges the root-count
bound for every actual polynomial factor.

`TupleComparison` extends the coprime splitting and kernel comparison to
independent choices in every coordinate. `WeightTruncation` proves closure of
the weighted-mass cutoff and dagger restrictions under this splitting, establishes
cross-coordinate coprimality, and reindexes the sum of fibers exactly.
`multivariable_totient_comparison_real` in `MultivariableComparison` proves the comparison
for arbitrary positive column exponents and every real cutoff.
`PolynomialSystem.totient_comparison_uniform` in `ComparisonUniformity` then
instantiates the actual polynomial system and bounds the constant by
`totientComparisonBound B ε g D`, where `g=deg Q` and `D` is the restricted bad
discriminant. It has no remaining root-count or comparison hypothesis.
`PolynomialSystem.totient_comparison_theoremOne_parameters` derives the required
small-exponent condition from Theorem 1's hypotheses and uses its admissibility
exponent `εδ/3` directly.

Thus the corrected **global multivariable totient comparison** is proved under
`g ε < 1`. The proof neither invokes the false printed lemma nor silently
strengthens its statement. The cutoff-dependent twist in Corollary 6 now also
has a separate valid comparison in `SelectedTiltComparison`.

Both the [author's PDF](https://tenenb.perso.math.cnrs.fr/PPP/ShortSums.pdf)
and the [published version, p. 129](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6559-11511_2006_Article_BF02392880.pdf)
display the unweighted hypothesis. This issue does not by itself refute Theorem 1.

Theorem 1's statement is `TheoremOne` in `Targets.lean`; its proof is
`theoremOne` in `TheoremOne.lean`. The separate reduction
`bound_of_normalized_bound` allows a homogeneous estimate to be proved only for
`F(1)=1`; the final proof instead works directly with every admissible `F`.

`PrimeLogSums` proves the elementary estimate
`∑_{p≤z} log(p)/p ≤ log(4)(1+log z)` from Chebyshev's bound and partial
summation. It also bounds `∑_{p≤z} (p^(κ/log z)-1)/p` uniformly in `z≥2`.
`TiltedAuxiliary` proves convergence of the root-weighted exponential moment
when `γ_h(ε+β)<1`, its finite smooth Euler product, and the exact local
increment as a difference of convergent series.
`localMomentError_product_uniform` in `MomentPrimeBounds` bounds the moment
correction product uniformly in `z` when the tilted exponent is at most a fixed
`σ<1`. First powers use the weighted prime sum; higher powers use a fixed finite
set of small primes and an inverse-square majorant at large primes.
`moment_exponent_gap` proves the choice `σ=7/8` from `γ_h ε≤1/8` and
`z≥4^(γ_h κ)`. `PolynomialSystem.factor_moment_product_bound` instantiates this
at every actual polynomial factor, using the stronger common threshold
`z≥4^(gκ)`.

`PrimePowerComparison` expands valuation-dependent prime increments over whole
prime-power splittings. Its finite convolution estimate retains a separate
prime-support domain in each coordinate. `MomentKernel` proves that the resulting
kernel has exactly the local moment-error Euler factors above and bounds every
finite smooth partial sum by that convergent product.

`smoothWeightUpTo_moment_uniform` in `SmoothMoment`
proves the **global finite root-weighted moment comparison** on smooth dagger
tuples. `smoothWeightUpTo_tail_uniform` then proves the Rankin saving
`exp(-κ log x / log z)`, uniformly in the finite mass bound `N` and smoothness
cutoff `z`. `PolynomialSystem.smooth_tail_bound` discharges the root-count
hypotheses and exponent gap at the common threshold `z≥4^(gκ)`.
`SmoothWeightSum` proves exact reindexing, including equivalence between
smoothness of the weighted mass and of every coordinate.
`PolynomialSystem.weight_smooth_tail_bound` expresses the resulting bound using
the paper's weight (16): the tail `x<n≤N, P⁺(n)≤z` is bounded by the exponential
saving times an explicit constant times the sum `n≤N, P⁺(n)≤z`.

`PrimeBandBounds` controls the un-tilted auxiliary Euler product on `w<p≤z`
by a constant depending on an upper bound for `log z / log w`. First powers
use the logarithmic prime estimate; higher powers have a summable majorant
`p^(2σ-2)` when `γ_h ε≤σ<1/2`.
`smoothWeightUpTo_cutoff_uniform` in `SmoothCutoffComparison` applies this to
an injective whole-prime-power split, preserving the finite mass bound and the
full dagger condition.

`SmoothTruncation` chooses an explicit scale `L` and the smaller cutoff
`w=z^(1/L)`. Its moment tail is at most half of the smaller smooth sum, allowing
that tail to be absorbed. `SmoothTruncationUniform` handles the remaining bounded
range of `z` with a fixed Euler product. The resulting
`smoothWeightUpTo_truncation_uniform` reduces every finite root-weighted smooth
sum to a sum with mass at most `z`, for all `z≥2`, uniformly in the finite mass
cutoff and the admissible arithmetic function.

`root_weight_smooth_tail` in `RootSmoothTail` proves convergence of the infinite
root-weighted tail and the bound
`∑_{n>x, P⁺(n)≤z} v(n;F,ρ) ≤ C exp(-κ log x / log z) ∑_{n≤z} v(n;F,ρ)`.
Its explicit positive constant `rootSmoothTailBound` depends on `A,B,κ`, the
exponent totals, a bound for those totals, and uniform prime-power root bounds;
it is independent of `F,x,z,ε`. It assumes `γ_h ε≤1/8`, `z≥2`, and
`z≥4^(Gκ)` with `G≥γ_h` for every coordinate.
`PolynomialSystem.root_smooth_tail` discharges the root-count hypotheses and uses
`G=deg Q` and `C_h=max(deg R_h,D³)`. Both dagger restrictions remain in the weight.

`TiltedTotientComparison` proves that the corrected totient comparison remains
uniform after exponential tilting. The prime correction contributes an extra
reciprocal prime, giving a summable majorant `p^(σ-2)` for any fixed `σ<1`.
`totient_weight_smooth_tail` in `TotientSmoothTail`
combines this with the root moment and truncation bounds. It proves convergence
and the infinite-tail estimate for the totient-modified root vector, with the
**original, untwisted root weight** in the truncated right-hand sum.

`SmoothTailUniformity` takes a finite envelope over the possible exponent totals
and root bounds. This gives the positive constant `smoothTailUniformBound A B κ g D`,
which is independent of the individual factors, their coefficients, `F`, `x`, `z`,
and the admissibility exponent. Both `PolynomialSystem.root_smooth_tail_uniform`
and `PolynomialSystem.totient_smooth_tail_uniform` use this constant.
`PolynomialSystem.totient_smooth_tail_theoremOne_parameters` derives the required
small-exponent condition from Theorem 1's assumptions and applies the estimate
to admissibility exponent `εδ/3` directly.

Thus the **root-vector and totient-modified specializations of Lemma 2** are
proved under the common threshold `z≥4^(gκ)`, including all the uniformity needed
for their application in the main proof.

`FloorRootArithmetic` proves that prime-factor flooring roots are multiplicative
on coprime inputs, divide their input, and recover `n` from `n^d`. Composing a
scalar admissible function with this root retains its growth parameters.
`AppendArithmetic` proves admissibility for products on disjoint coordinate
blocks and defines the paper's scalar class `M`, with one prime-factor constant
and a polynomial-growth constant for each positive exponent.
`LiftedWeights` appends a diagonal block of column sums to the exponent matrix.
Its new arithmetic function absorbs the scalar weights through flooring roots;
the new mass is exactly the square of the original mass, and the summands agree.
`LiftedWeightSums` compares the smooth tails and the truncated right-hand sums.
`GeneralSmoothTail` applies the proved root-vector estimate with decay parameter
`κ/2`, retaining both `exp(-κ log(x)/log(z))` and `4^(γκ)`.
`LemmaTwo` chooses common constants for the finite class-`M` family, derives the
small growth condition from Theorem 1's `εδ/3` parameters, and handles `z<2`
separately. The result `lemmaTwo : LemmaTwo` covers the full original range
`x > z > 4^(γκ)`, with `γ` the sum of the factor multiplicities. Its constant
is chosen before `F`, `D`, `x`, and `z`, and convergence of the infinite tail
is part of the conclusion. No multiplicativity of the scalar weights is assumed.

`PrimeThreshold.exists_prime_threshold` constructs the first crossing prime in
(28), retains whole prime powers, proves separation of the prime supports, and
proves that the crossing prime divides the complementary mass. The accompanying
dichotomy explicitly includes the case where the total mass is below the threshold.

`DiscriminantSplitting` supplies the correct coprime removal of discriminant
primes from tuples dividing polynomial values. The remainder satisfies the full
dagger condition; the removed part is supported on the restricted bad discriminant.
The decomposition supports both the arithmetic and root-weighted majorant bounds.
The single-gcd removal written in the estimate of `S₁` does not generally provide
the needed coprimality: `gcd_removal_not_coprime` checks that dividing `8` by
`gcd(8,4)` leaves a factor sharing a prime with both `4` and the removed gcd.
The full-prime-power replacement is proved. `BadPrimeMass` also proves convergence
of the entire removed-part series with the congruence density
`ρ_radical(lcm(u₁,…,u_r))/lcm(u₁,…,u_r)` retained. The bound depends only on
`B`, total degree `g`, and the restricted bad discriminant `D`, assuming
`g²ε≤1/8`. It uses `lcm(u)≥(∏u_i)^(1/g)` and the fractional auxiliary Euler
products in `FractionalAuxiliary`; thus it covers arbitrarily large, shared
bad-prime valuations.

`JointCongruence` proves the CRT interval estimate for different polynomial
conditions at pairwise coprime moduli. After removing the full bad-prime parts,
it bounds the original simultaneous conditions by the radical condition at
`lcm(u)` together with the individual good-coordinate conditions. If
`lcm(u)·∏v_i≤b−a`, the interval error is absorbed into twice the main term.
`BadPrimeCongruence.badPrime_weighted_congruence_sum_le` (in namespace
`PolynomialSystem`) sums the bad parts and retains the good tuple's original
root weight, with a constant uniform in all removed valuations. This supplies
the corrected bad-part counting estimate. The additional sieve restriction
and the four contributions in the main proof remain to be handled.

`SelbergWeights` constructs the optimizing Selberg coefficients by Möbius
inversion over multiples. It proves normalization at `1`, support up to a real
cutoff `R`, and the exact main quadratic form `1/G(R)`, where `G(R)` is the
truncated sum of Selberg terms. The squared coefficients vanish beyond `R²`,
and the resulting upper bound includes an explicit remainder sum restricted
to that level. This extends Mathlib's diagonalization identity with actual
optimizing weights.

`SelbergDenominator` proves the exact logarithmic moment of the full divisor
sum and uses it to bound the omitted tail. If the sieve primes are at most `z`,
`ν(p)≤g/p`, and `log z≥16`, the cutoff `R=z^(2g)` retains at least one quarter
of the full Euler product. Thus the optimized main coefficient is at most
`4∏(1−ν(p))`.

`SelbergCoefficientBounds` bounds each coefficient by its local sifting
correction. With the integral-density gap `ν(p)≤1−1/p`, it obtains uniform
subpolynomial majorants, using `PrimeFactorBounds`. `SelbergRemainder` sums
paired least-common-multiple contributions and proves
`S ≤ 4X∏(1−ν(p)) + C K z^(4g(1+η))`, where `K` depends only on `g,η`, and
`|remainder(d)|≤C g^ω(d)` is required only on divisors of the sieve prime product.
The coefficient sum, its support, and the remainder bound are all proved.

`PolynomialSieve.exists_polynomial_sieve_bound` (in namespace `NairTenenbaum`)
instantiates this for a polynomial with no fixed prime divisor and degree at
most `g`. It counts polynomial values over arbitrary integer intervals by
fiber multiplicities, without any injectivity assumption. The congruence
remainder is discharged with `C=1`, yielding constants independent of the
polynomial coefficients and interval. Primes with no roots are omitted from
the sieve prime product.

`ConditionalPolynomialSieve` also proves the version with simultaneous
polynomial divisibility constraints at pairwise coprime positive moduli. The
sieve primes must be coprime to their product. CRT gives the exact main density
`∏ρ_Ri(m_i)/m_i` and remainder numerator `∏ρ_Ri(m_i)`; both are retained in the
quantitative bound. The uniform constant depends only on `g,η`, even when the
conditioning polynomials and moduli vary. This can accommodate the radical
condition at the bad-part LCM as one coordinate.

`OmittedEulerFactors` proves that the inverse Euler factors omitted at primes
dividing a modulus `n` are at most `omittedEulerBound g · (n/φ(n))^g`.
The constant is explicit and depends only on the degree bound. The proof
separates primes at most `2g` from a summable `O(g²/p²)` correction at larger
primes. `SievePrimes` constructs the actual squarefree sieve modulus, omitting
modulus primes and root-free primes, and restores the full `sieveProduct Q z`
in the conditional sieve estimate. No hypothesis on the selected prime set
remains in that theorem.

`SieveProductLowerBound` proves `sieveProduct(Q,z)⁻¹≤C z^δ` for every `δ>0`,
uniformly in polynomials of bounded degree with no fixed prime divisor.
`SieveLevel` then absorbs the conditional sieve remainder whenever
`B·mass(m)·z^(4g(1+η)+δ)≤b−a`. Its resulting bound is a constant times
`(b−a)·sieveProduct(Q,z)·(mass(m)/φ(mass(m)))^g·∏ρ_Ri(m_i)/m_i`.
Both constants depend only on the degree and the chosen exponents.

`BadPrimeSieve` combines the conditional sieve with the full bad-prime
summation. It uses the radical congruence at `LCM(u)` and the good coordinate
congruences, retaining the density `ρ_radical(LCM(u))/LCM(u)`. The totient
correction for the bad part is bounded using its prime support. Every valuation
of every bad prime is summed with the convergent auxiliary kernel.
`SmallDivisorSieve` then sums over the good tuples and removes their totient
correction using the proved comparison theorem.

`SmallDivisorSum` starts with the unsplit divisor tuples of weighted mass at
most `N`. Tuples with positive sifted counts acquire the required discriminant
coprimality from an actual polynomial value; the others contribute zero.
Full prime-power splitting injects the contributing tuples into the bad/good
sum. Its final theorem needs just one sieve level,
`L·N·z^(4g(1+η)+δ)≤b−a`, and bounds the original sifted tuple sum by the
original truncated weight sum. This completes the corrected sieve estimate
needed after splitting the small-divisor contribution, without the invalid
single-gcd removal.

`SieveScales` specializes to `η=1/16`, `δ=1/4`,
`N≤x^(3g²ε/2)` and `z=x^(gε/2)`. The combined exponent is at most
`15g²ε/4`, leaving a gap below `y≥x^(4g²ε)` to absorb both the sieve
constant and integer-endpoint rounding. The resulting lower threshold on `x`
is uniform in the polynomial coefficients. `SieveCutoffComparison` restores
the factors between `x^α` and `x` at a cost bounded by
`exp(4g log(4)/α)`, once the smaller cutoff is sufficiently large.
`SmallDivisorMainTerm.exists_smallDivisorSiftedSum_mainTerm_bound` (in namespace
`NairTenenbaum`) combines these results with weight-sum monotonicity. It bounds
the sifted small-divisor sum by a constant times `mainTerm P F x y`; the constant
is uniform in the coefficients and arithmetic function and has an explicit
factor depending on the restricted discriminant.

`RoughMass` proves `z^Ω(n)≤n` for integers supported on primes at least `z`.
At `z=x^α` and `n≤x^c`, this bounds the remaining arithmetic weight by
`A^(c/α)`. `PolynomialValueTuples` identifies the weighted mass of the
irreducible value tuple with `|Q(t)|` and proves the actual sieve coprimality
of every selected prefix whose cutoff exceeds `z`. `SmallDivisorMajorant`
groups integers by their selected tuple, allowing arbitrary fiber sizes, to
prove the reduction in (31).

`FirstContribution` defines the small rough-prefix class and proves its
reduction to the sifted divisor sum. `FirstContributionReal` identifies real
mass cutoffs with positive integral cutoffs. `ValueBoundContributions` supplies
the bound under an explicit value-growth hypothesis. `PrimeArgumentHeight`
absorbs the evaluation constant into `x^(1/8)` and gives the common height
threshold used by Theorems 1 and 3.

`PrimePowerThreshold` handles the second class. It constructs the least
exponent with `p^ν>T` and proves `p^ν≤pT`. The degree identity bounds the
sum of the multiplicities of the irreducible factors, so a large weighted
prime part forces `p^ν>T` in one coordinate. This accounts explicitly for
repeated irreducible factors. `SecondContributionCounting` applies this to
small prefixes crossing the larger mass threshold and embeds the class into
`primePowerExceptionalSet`.

`PrimePowerCounting` proves an elementary union bound over primes at most
`z` and the irreducible coordinates. At `T=z³`, the exceptional count is at
most `4(b−a)g·max(g,D³)/z²`, provided `z⁴≤b−a`. The coordinate root bounds
are discharged using `PolynomialLocal`; no independence assumption is used.
`SecondContributionWeights` names the weighted sum over this exceptional set.
The pointwise bound in `ValueWeightBounds` and the exceptional count combine in
`ValueBoundContributions` to give a power saving, also when `g=1`.

`MainTermLowerBound` proves that the unit tuple contributes at least `F(1)`
and that any fixed negative power is absorbed by the uniform lower bound
for the sifting product. Consequently the second-class bound does not require
normalizing `F(1)`. `SecondContribution` supplies the prime-power scale identity
and sieve-level condition. The common value-bound estimates in
`ValueBoundContributions` keep the saving exponent as a parameter, and
`PrimeArgumentExceptional` specializes them to the margin `17gε/24` with a
saving `gε/24`. These estimates serve both integer and prime arguments.

`SmoothDivisorDensity` and `SmoothDivisorCounting` give a direct treatment
of the bounded-smoothness third class, avoiding the printed restriction
`x^ε₂/D^r<n` after bad-prime removal. For any divisor tuple `m`,
`weightedMass(m)≤LCM(m)^g`, and its least common multiple divides the
radical value. Thus a prefix of mass greater than `x^(3g²ε/2)` supplies a
smooth radical divisor greater than `x^(3gε/2)`. Its modulus is at most
`x^(3g²ε)`, which fits in the rounded interval for a uniform lower threshold.

On any fixed finite prime support `s`, the reciprocal-square-root series
has a bounded Euler product. The uniform radical root bound then gives a
reciprocal-density tail of order `T^(-1/2)`, with a constant depending only
on `g,D,s`. `ValueBoundContributions` combines this with the pointwise
arithmetic-weight estimate to obtain a power saving. It holds even
when the tuple coordinates share bad primes.

`ThirdContribution` defines the large smooth-divisor class and proves the
required sieve-level inequality. `IntegerIntervalDecomposition` places this
class inside the smooth exceptional set. The parameterized smooth-divisor
estimate in `ValueBoundContributions` preserves the combined prefix mass and
allows the finite support to be chosen before the final bound constant.

The fourth contribution requires a tail estimate that retains the mass of
all removed bad-prime powers. `BadPrimeMoments` proves a uniform bound for
`∑ K_bad(u)·weightedMass(u)^β` whenever `g²(ε+β)≤1/4`.
`SmoothMomentUniformity` exposes the good-tuple moment before applying the
tail inequality and bounds it by the original weight sum truncated at the
smoothness cutoff. `SplitSmoothTail` combines these two moments and proves
`exp(-κ log(X)/log(w))` decay for the condition
`X<weightedMass(u*v)`. In particular, the tail condition is on the original
prefix, rather than just the good part. A single sufficient cutoff condition
is `log(w)≥8g²κ`, together with the usual small growth exponent.

`SmoothTailSieveReindex` preserves this combined mass condition when splitting
original divisor tuples. `SmoothTailSieve.exists_smoothTailSiftedSum_bound`
(in namespace `NairTenenbaum`) supplies the resulting conditional sieve bound:
its right side is a constant times
`(b−a)·sieveProduct(Q,z)·exp(-κ log(X)/log(w))·∑_{n≤w}weight(n)`.
The smoothness cutoff `w` and sifting cutoff `z` are separate. The level is
`L·N·z^(4g(1+η)+δ)≤b−a`; `K,L` depend only on degree and the sieve exponents,
and the remaining explicit cost depends on growth parameters, moment strength,
degree, and the restricted discriminant.

The logarithmic-band part of the fourth contribution is now proved.
`LargePrefixScales` gives a uniform sieve level for `N≤x^(3g²ε)` whenever
`z≤x^(gε/16)`. Set `u=gε/16` and group the largest prefix prime into bands
with lower cutoff `z=x^α`, upper cutoff `w=x^(2α)`, and
`α=u/2^(j+1)`. `SmoothTailMajorant` removes the rough remainder while retaining
the original prefix's mass tail. `PrimeBandMajorant` and
`PrimeBandContribution` combine this with the smooth-tail sieve and Euler
comparison. A moment strength satisfying
`κ·(3g²ε/2)/2 ≥ c·log(A)+4g·log(4)+1`, where `c=g+1/δ+1`, leaves the
factor `exp(-1/α)`. This is bounded by `exp(-j)` and has a uniformly bounded
sum over any finite collection of bands (`PrimeBandDecay`,
`PrimeBandSummation`).

`PrimeBandCutoff` chooses the moment strength and a fixed lower prime cutoff
before all polynomial coefficients and discriminants. A band whose upper edge
exceeds that cutoff satisfies every logarithmic and size condition required by
the sieve, moments, and Euler comparison. `PrimeBandCover` assigns actual
prefixes with largest prime between the fixed cutoff and `x^u` to these bands.
The finite interval requires only finitely many bands; nonnegative weights
allow overlap. `IntermediateContributionReal` identifies the real and integral
cutoff predicates. `ValueBoundContributions` bounds the intermediate contribution
on arbitrary integer intervals; its constants precede the polynomial family.

`LargePrefixMainTerm` and `exists_largeRoughContribution_value_bound` cover every
prefix of mass at most `x^(3g²ε)` whose next-prime cutoff exceeds `x^(gε/16)`.
This includes the original first contribution, the upper-prime part of the
fourth, and the small-total-mass case.

`ShortSumDecomposition.prefix_classes_exhaustive` covers every nonzero total
polynomial value by four majorants. If the whole mass is small, use the
large-prefix rough-remainder bound. Otherwise take the first crossing prime.
A cutoff above `x^(gε/16)` again gives that bound. For a smaller cutoff, a
prefix below `x^(3g²ε/2)` gives the small-crossing-prime contribution. A larger
prefix is either supported on the fixed finite prime set or belongs to the
intermediate-prime contribution. The zero-extension terms vanish separately.
The majorants can overlap because the arithmetic weights are nonnegative.

`IntegerIntervalBound.exists_integerSum_mainTerm_bound` combines the
four estimates with the growth margin `cσ≤17gε/24`. Theorem 1 now applies this
integer-interval bound through the same height-to-interval threshold lemma
used by Theorem 3. The former separate real-interval estimate chain has been
removed. The statement in `Targets.lean` is unchanged: growth parameter `εδ/3`,
interval range `x^(4g²ε)≤y≤x`, and a coefficient-independent height threshold.

`SiftedDivisorSplit` provides one reindexing proof for all four ordinary and
mass-tail split lemmas, and one fiber-counting proof for the four selection
lemmas. `ConditionalPolynomialSieve` specializes `LocalConditionalSieve`.
`absorb_sieve_remainder` handles both sieve-level remainder arguments, while
common finite-sum moment and dyadic-band lemmas serve both pipelines.
`PolynomialSystem.sum_roughPrefix_le_of_selected_sum` combines the rough
remainder bound with any selected-prefix estimate. The bad-prime sieve and
smooth-tail arguments share `weighted_count_le_badPrimeKernel`, and the mass
and moment estimates share `sum_prod_fractionalAuxiliary_le`.
`exists_sieve_scale_threshold` supplies the common analytic threshold from an
explicit exponent gap. `exists_finset_sum_le_cover` assembles both finite band
covers, while `primeBand_decay_of_margin` leaves the required exponential decay
after paying the arithmetic and Euler-product costs. The prime-specific
reciprocal logarithm, constant-term hypothesis, and totient exponents remain
explicit in their application lemmas.

`AffineRootCounts` begins the arithmetic-progression applications. It proves
that substitution by `qX+a` preserves root counts at moduli coprime to `q`,
and gives zero root count at all other moduli when `(q,Q(a))=1`. The transformed
sieve product is exactly the original product with primes dividing `q` omitted.
`AffinePolynomialSystem` constructs the substituted family: a rational affine
algebra automorphism preserves irreducibility and nonassociation, while the
original exponent matrix, unit signs, and total degree are retained.

`AffineDiscriminant` proves the affine resultant identity by transport to a
splitting field and deduces the exact discriminant multiplier `q^(d(d−1))`,
including degree zero. `AffineBadDiscriminant` uses the zero root counts at
primes dividing `q` to prove that the new restricted discriminant divides the
original one. `AffineWeights` proves the exact weight identity: the new weight
is the old weight for masses coprime to `q` and zero otherwise.

The progression estimate uses a direct bound on the actual values, rather than
requiring a coefficient-height hypothesis for the transformed polynomial at a
smaller scale. `ValueBoundContributions` supplies all four majorants from
`|Q(t)|≤x^c`. `IntegerIntervalDecomposition` gives their exhaustive cover on
any integer interval. `IntegerIntervalBound` absorbs the bounded range of `x`
into the bound constant. The resulting
estimate holds for every `x≥2` with rounded length bounds `y−1≤b−a≤2y`.
Its analytic scale is independent of the interval's location.

`ProgressionIntervals` maps the original progression into the integer interval
with endpoints `floor((x−a)/q)` and `floor((x+y−a)/q)` and identifies its main
term exactly. `ProgressionBound` uses the original scale, with interval exponent
`εβ`, value exponent `g+1/(2δ)+1`, and arithmetic growth `εβδ/6`. The modulus
restriction supplies the lower length bound. The height threshold can be chosen
as `max 2 ((g+1)2^g)`, before `β`; a finite envelope converts the transformed
restricted-discriminant dependence to dependence on the original one.
`CorollaryOne.corollaryOne` proves the recorded Corollary 1 proposition.

`IrreducibleSystem` constructs the identity-exponent polynomial system for an
irreducible pairwise coprime family. It also proves that no fixed prime divisor
implies primitivity, so Gauss's lemma transfers integral irreducibility to the
rational factor interface. `IrreducibleProgressionWeights` reindexes the scalar
weight sum exactly as the tuple sum in (20), including the discriminant and
progression-modulus restrictions, for every real cutoff. `CorollaryTwo` proves
the numbered result directly for integer polynomials; it requires no separately
supplied factorization data.

For Corollary 3, `ProductArithmetic` proves that the coordinate product of
functions in `M₁(A,B,σ)` belongs to `Mₖ(A,B^k,σ)`, and that zero extension
commutes with this product. `DivisorTupleDisjointness` proves uniqueness of a
discriminant-coprime divisor tuple at a given integer and weighted mass:
cross-coordinate coprimality removes all other coordinates from the weighted
divisibility relation. `JointDensityComparison` derives a finite disjoint-union
density inequality from the already proved CRT counting formula, letting the
integer interval length absorb its fixed remainder.

`SubstitutionDensity` proves that pairwise coprime original polynomials have
disjoint exponent supports, and hence substituted dagger tuples are pairwise
coprime. It then aggregates **all** factor tuples with the same substituted
arguments and bounds their total root density by the product of the original
polynomial root densities. This handles multiplicities of the substitution
map before any enlargement of summation domains.

`FactoredWeightBound` applies that fiber estimate and enlarges the remaining
mass cutoff to a box, giving the product of one-variable sums for every real
cutoff, including cutoffs below one. `CorollaryThree` combines this comparison
with Theorem 1 and the product-admissibility lemma. All constants are chosen
before the polynomials and arithmetic functions; only the bound constant
depends on the restricted discriminant.

`FamilyFactorization` constructs equation (9) for every original integer
polynomial family with no fixed prime divisor. The common finite factor set
is the union of the normalized factors of its members. Factor multiplicities
supply the exponent matrix and polynomial units supply signs of absolute value
one. Every chosen factor inherits the no-fixed-prime condition, hence is
primitive and irreducible over the rationals. Gauss's divisibility lemma and
normalization give rational nonassociation of distinct factors. This includes
constant unit polynomials and empty families.

`FamilyTheorems` applies the existing uniform bounds to that constructed
system. Its Theorem 1 and Corollary 1 statements even retain the stronger
parameter ranges proved in the general bounds. The original polynomials are
the only polynomial input; the selected factorization defines the weight and
restricted discriminant without adding any existence assumption.

For Theorem 3, `PrimeArgumentRoots` proves the exact prime-modulus identity
`ρ_(QX)(p)=ρ_Q(p)+1` away from divisors of `Q(0)`, and equality of root counts
at divisors of `Q(0)`. It also verifies a missing hypothesis in the printed
reduction: `Q=X+1` has no fixed prime divisor and `Q(0)=1`, but `XQ` has the
fixed prime 2. Thus Theorem 1 cannot simply be applied to the enlarged family.
This does not refute Theorem 3.

`PrimeArgumentEuler` proves the elementary bound
`∏_(p≤x)(1−1/p)≤1/log(x)` by embedding the harmonic sum into the convergent
finite-prime Euler product. Omitting divisors of a nonzero integer costs at
most its exact reciprocal-totient ratio. These results give the required
`|Q(0)|/φ(|Q(0)|)` correction and logarithmic saving.

`LocalConditionalSieve` proves the conditional Selberg bound assuming strict
root-density bounds only at the selected primes. `PrimeArgumentSieve` selects
primes outside the prefix modulus and `(g+1)!`, proves that all remaining
primes are admissible for `XQ`, and restores the original `Q` Euler product.
The resulting main term has an additional `1/log(z)` factor and a totient
twist of exponent `g+1` on the prefix modulus. The remainder has sieve exponent
`4(g+1)(1+η)`. The constant depends only on `g,η`; the dependence on `Q(0)`
stays explicit. Actual prime arguments above `z` satisfy the enlarged sieve
condition whenever they satisfy the original polynomial sieve condition.

`PrimeArgumentSieveLevel` absorbs this remainder at level
`L·mass(m)·z^(4(g+1)(1+η)+δ)≤b−a`. The extra logarithm is absorbed into the
arbitrarily small power `δ`, without a threshold depending on `Q(0)`.
`TotientComparisonExponents` separates the twist exponent from the degree,
giving uniform comparison for every fixed twist exponent with the original
growth condition `gσ<1`. `PrimeArgumentMajorant` groups selected prefixes at
prime arguments into the enlarged sifted tuple sum; its pointwise value bound
uses only the original polynomial family.

`PrimeArgumentBadSieve` retains the original radical LCM density while summing
all bad-prime coordinates. `PrimeArgumentSmallSieve` applies the independent
totient-exponent comparison, and `PrimeArgumentSmallSum` reindexes the good
and bad parts back to the original divisor tuples. The new factor remains
explicit throughout; the bad-prime constant still depends on the original
restricted discriminant.

`PrimeArgumentScales` supplies a uniform sieve level for all prefix masses
up to `x^(3g²ε)` and every cutoff at most `x^(gε/16)`. This smaller cutoff
accommodates the sieve dimension `g+1` with the original length condition
`y≥x^(4g²ε)`. `PrimeArgumentMainTerm` transfers the bound to the exact
Theorem 3 main expression and proves that every fixed power saving is
absorbed by it, uniformly in `Q(0)`. `PrimeArgumentFirstContribution` proves
the resulting small-prefix contribution bound for actual prime arguments.

`PrimeArgumentMoment` and `PrimeArgumentSplitTail` prove the smooth moments
with the additional totient power, retaining the entire bad-prime mass before
taking the tail. The growth assumptions use the original degree; only the
finite envelope for the good-part constant uses degree plus one.
`PrimeArgumentTailReindex` and `PrimeArgumentTailSieve` combine this with the
new conditional sieve, with separate smoothness and sifting cutoffs.

`PrimeArgumentTailMajorant` and `PrimeArgumentBandContribution` bound the
actual arithmetic weights in each logarithmic band. `PrimeArgumentBand`
increases the free moment margin from one to two: the extra exponential
decay absorbs the factor `1/α` from `log(x^α)=α log(x)`. Thus
`PrimeArgumentBands` sums any finite collection of eligible bands with a
constant independent of the number of bands. Its moment strength and lower
smoothness cutoff are chosen before the polynomial family.

`PrimeArgumentCover` covers the intermediate-prefix contribution by those
prime-restricted bands. `PrimeArgumentExceptional` gives a power saving for
the two unrestricted exceptional contributions with value-growth margin
`17gε/24`. `PrimeArgumentDecomposition` proves the exhaustive four-contribution
cover, and `PrimeArgumentIntervalBound` assembles the bounds on integer intervals.
`PrimeArgumentHeight` absorbs the polynomial degree constant into an exponent
`1/8`; the resulting value-growth exponent `g+1/δ+1/8` is compatible with the
paper's admissibility exponent `εδ/3`, including degree one and `δ=1`.
`PrimeShortSum` handles the real interval endpoints, and `TheoremThree` proves
the final coefficient-uniform theorem. `PrimeFamilyTheorem` exposes the result
for the original polynomial family. Retaining that family throughout avoids
strengthening the growth hypothesis when adding `X` in the sieve.

`ShiftedLinearSystem` constructs the system for `X+a`, proves its discriminant
is one and its weight is `F(n)/n`, and computes its height as `max(1,|a|)`.
The one-root Euler bound gives the second reciprocal logarithm.
`CorollarySeven` proves the shifted-prime estimate with constants independent
of the nonzero shift and arithmetic function. Its interval range is
`x^(4ε) ≤ y ≤ x`, correcting the transposed inequality in the printed corollary.

`GoldbachSieve` bounds representations `p+q=N` directly using the conditional
prime-argument sieve for `(X-N)X`, without a height restriction. Representations
with either prime at most the cutoff `z` contribute at most `2(z+1)`. All other
representations satisfy the sieve condition, giving an absolute-constant bound
by `(N/φ(N))y/log²(z)+z^9`. `GoldbachScales` chooses `z=N^(θ/18)` when `y≥N^θ`,
absorbs the error using `log²(N)≪_θ N^(θ/2)`, and handles bounded `N` by the
interval cardinality. `CorollaryTen` takes `θ=δε`, yielding the original
Goldbach statement, uniformly in `N,x,y`.

For Corollary 6, `SelectedMoment` proves a moment estimate on the full
weighted-mass truncation, tilting only primes below a selected cutoff. Unlike
the earlier smooth-domain moment, the sum includes nonsmooth integers.
The selected convolution kernel vanishes outside the chosen prime support,
so its finite sum is bounded by the existing convergent moment Euler product.
`SelectedTilt` proves complete multiplicativity on positive integers and
admissibility with parameters `A exp(κ), B, σ+κ/log(z)`.
`SelectedTiltComparison` proves equation (41) directly, with constants depending
only on degree, growth parameters, moment strength, and restricted discriminant.
This supplies the Corollary 6 application without invoking the false general
Lemma 1.

`PolynomialPreimages` bounds every absolute-value fiber of a nonconstant
integer polynomial by twice its degree. It gives a uniform small-value count
even near roots. `FixedSmoothCounting` bounds values on any fixed finite prime
support by an arbitrarily small power of the value cutoff.
`SmoothValueRankin` preserves zero extension and separates a small-value
remainder before applying the tilt. `SmoothValueExceptional` and
`SmoothValuePowerBounds` bound the weighted exceptional terms by
`C x^(7q/8) F(1)`, where `q=g²ε`. The original lower bound on `z` implies
`exp(-κ log(x)/log(z)) ≥ x^(-3q)`. Since `y≥x^(4q)`, the main-term lower bound
absorbs these exceptional terms, including a further `x^(-q/8)` margin.

`SmoothTiltBound` applies Theorem 1 to the admissible tilt once `z` exceeds
a fixed cutoff. `CorollarySix` uses moment strength `8κ/q` and separates values
at `x^(q/8)`, obtaining the exact saving `exp(-κ log(x)/log(z))`. For smaller
`z`, the fixed-prime-support count gives the same bound. The constants are
chosen before the polynomial family, and `SmoothFamilyTheorem` constructs
the factorization data for the original families.

The restricted coordinate must be nonconstant. The general family interface
allows constant units, and §2 does not explicitly exclude them.
`constant_coordinate_smooth_bound_fails` in `CorollarySixObstruction` proves
failure for `(Q₁,Q₂)=(X,1)` and `F=1`, with admissible parameters
`ε=1/16`, `δ=1`, `κ=log(2)/16`, and `z=2`. The smooth sum is exactly `x`
at integer scales with `y=x`, the main term is at most `x`, and the claimed
saving is `x^(-1/16)`. Thus `corollarySix` records nonconstancy explicitly.

`HooleyShortSum` specializes the proved short-sum theorem to every positive
power of Hooley's function and every positive interval exponent. It proves
`Σ Δ(|Q(n)|)^t ≪ y · sieveProduct(Q,x) · Σ Δ(m)^t ρ_Q(m)/m` for any fixed
positive-degree polynomial with no fixed prime divisor. The zero-extension
identity is checked also at polynomial roots. No irreducibility is required
for this intermediate root-weighted bound.

`HooleyPrimeShortSum` proves the shifted-prime counterpart, retaining the
factor `|a|/φ(|a|)` and `y/log²(x)`. Choosing height exponent `1/2` gives a
threshold independent of `a` throughout `1≤|a|≤x`.

`DivisorSumRearrangement` proves the exact identity between the floor sum in
Corollary 5 and the sum of dyadic divisor-window counts. `PrimeProgressionRearrangement`
proves the analogous identity for differences of prime counts in residue
classes. Its condition `a≤x` excludes the diagonal prime `p=a`, whose zero
difference is divisible by every modulus. Both identities include rounded
endpoints, and their Hooley upper bounds are uniform in the dyadic cutoff.

`HooleyAverageReductions` combines these identities with the short-sum results
and the elementary Euler bound for `X`. The Corollary 5 expression is at most
`C y/log(x) · hooleyRootSum X 1 x`; the Corollary 9 expression is at most
`C (|a|/φ(|a|)) y/log²(x) · hooleyRootSum X 1 x`, uniformly for nonzero
`|a|≤x`. These are unconditional intermediate bounds. The sharp weighted
Hooley mean estimate has not been substituted by an assumption or axiom.

The weighted mean proof follows Lemma 2.2 of Tenenbaum,
*[Sur une question d’Erdős et Schinzel, II](https://tenenb.perso.math.cnrs.fr/PPP/Erdos-Schinzel2.pdf)*,
Inventiones Mathematicae 99 (1990), 215–224, reference [9] of the main paper.
`HooleyMoments` constructs `M_q(n)=∫ Δ(n,u)^q du` from finite interval
indicators. `HooleyMomentComparison` proves
`Δ(n)^q ≤ 2^(q−1) M_q(n) ≤ 2^(q−1) τ(n)^q`, and positivity for nonzero `n`.
These prove the moment comparison (2.6), including boundary conventions.

`HooleyMomentRecurrence` proves the exact expansion at a coprime prime:
`M_q(pn)=2 M_q(n)+E_q(n,p)`. `HooleyMomentInterpolation` bounds intermediate
moments by powers of the first and `q`th moments. `PrimeLogIntervals` uses the
proved Chebyshev estimate to bound `Σ log(p)/p` in every interval of logarithmic
length two by `log(4) exp(2)`. `HooleyPrimeSampling` combines that overlap bound
with the local integral comparison. Thus `HooleyPrimeMixedBound` proves, for
any finite prime set and `q>1`,
`Σ (log(p)/p) E_q(n,p) ≤ log(4) exp(2) 4^q τ(n)^(q/(q−1)) M_q(n)^((q−2)/(q−1))`.

`HooleyWeightedPrimeStep` includes the root weights `ρ_Q(p)/p^σ` for `σ≥1`,
using `ρ_Q(p)≤deg(Q)` only in the error. The main prime sum remains explicit.
`WeightedMomentPowers` proves the finite weighted concavity inequality and the
fractional-power prime step for `0≤θ≤1`; it retains the coprimality condition
where required by the recurrence. This establishes the finite mixed-term
estimate used in (2.10), without assuming a prime-ideal asymptotic.

`HooleyDirichletCoefficients` defines the squarefree coefficients
`a_q(n)=M_q(n)^(t/q)ρ_Q(n)` and proves `a_q(n)≪ n^η` for every `η>0` and `t≥0`,
with constants independent of the positive moment order `q` and polynomial
coefficients at bounded degree. `HooleyDirichletSeries` proves convergence of
`L(σ)=Σ a_q(n)n^(−σ)` and `Σ a_q(n)log(n)n^(−σ)` for `σ>1`, and `L(σ)≥1`.
`HooleyDirichletDerivative` proves
`L′(σ)=−Σ a_q(n)log(n)n^(−σ)` using a summable derivative majorant on a smaller
half-line.

`PrimeFactorReindex` constructs the equivalence between an integer with a
selected prime divisor and a prime with a positive cofactor. Nonnegativity,
squarefree support, and convergence of the logarithmic sum justify the double
series reindexing. `HooleyDirichletPrimeExpansion` proves (2.9), including
absolute convergence in both summation orders and the precise conditions
`Squarefree(m)` and `p∤m`. The natural-number version includes the zero term
explicitly, where it vanishes.

`HooleyInfinitePrimeStep` proves convergence of
`P(σ)=Σ_p ρ_Q(p)log(p)/p^σ` for `σ>1` and passes the fractional-moment prime
step to all primes. `SeriesInterpolation` supplies Hölder interpolation for
nonnegative convergent series. `HooleyDirichletError` applies it to the mixed
error, proving its convergence and bounding it by
`C_q^(t/q) D(σ)^(1/(q−1)) L(σ)^(1−1/(q−1))`, where
`C_q=deg(Q) log(4) exp(2) 4^q` and
`D(σ)=Σ_{n squarefree} τ(n)^t ρ_Q(n)/n^σ`.

`HooleyDifferentialInequality` therefore proves the unconditional inequality
`−L′ ≤ 2^(t/q) P L + P^(1−t/q) C_q^(t/q) D^(1/(q−1)) L^(1−1/(q−1))`
for `σ>1`, `q>2`, and `0≤t≤q`.

`SquarefreeEulerBound` injects each squarefree integer into its prime-factor
set, bounding finite sums by the corresponding product of `1+a(p)` and then
by `exp(Σ a(p))`. For summable nonnegative prime weights this also proves
convergence of the squarefree series. `HooleyDivisorEulerBound` applies the
bound to obtain `D(σ)≤exp(2^t R(σ))`, where
`R(σ)=Σ_p ρ_Q(p)/p^σ`. The prime series converges for `σ>1`. Every positive
moment order has `L(σ)≤D(σ)`, with no loss depending on the order.

`RootPrimeSeriesDerivative` proves `R′(σ)=−P(σ)` and the finite-interval
integral identity between these two series. `DifferentialInterpolation` and
`HooleyIntegratingFactor` use this exact identity: with `θ=t/q`, `h=1/(q−1)`,
and `U=exp(−2^θ h R)L^h`, they prove
`−U′≤h C_q^θ P^(1−θ) exp((2^t−2^θ)h R)`.
`HooleyIntegratedBound` proves integrability of this majorant on every compact
interval inside `(1,∞)` and the unconditional endpoint estimate
`U(a)≤U(b)+∫_a^b h C_q^θ P(s)^(1−θ) exp((2^t−2^θ)h R(s)) ds`.

This integrating factor is a variant of the source differential argument.
It permits using an elementary pole bound on `P` rather than requiring a
leading constant of one there. `PrimeDirichletPoleBound` groups primes by
`floor(log(p))`, uses the proved logarithmic-interval mass estimate, and sums
a geometric series. It proves
`P(σ)≤2 deg(Q) log(4) exp(2)/(σ−1)` for `1<σ≤2` and substitutes this into the
majorant.

The sharp logarithmic bound on `R` is now proved. `ResidueHomKernels` shows
that a homomorphism to `ℤ/nℤ` is determined by its kernel and that the kernel
quotient has cardinality `n`. `ConductorQuotient` extends the polynomial
quotient description to every modulus coprime to the conductor exponent.
`NumberFieldResidueRoots` uses it to inject minimal-polynomial residue roots
into ideals of the corresponding norm. `ConductorNonzero` proves that an
integral primitive generator has nonzero conductor exponent by clearing
denominators with its power-basis discriminant.

`IdealNormDirichlet` proves convergence of the real ideal-norm Dirichlet
series, identifies it with Dedekind zeta, and deduces a bound `C/(σ−1)` from
Mathlib's proved residue theorem. `MinpolyEulerProduct` expands finite Euler
products over squarefree prime sets and bounds their coefficients by ideal
counts. `PrimeProductLogBound` bounds the logarithmic error by a convergent
quadratic series. `MinpolyPrimeLogBound` restores the finitely many conductor
primes and proves `R(σ)≤C−log(σ−1)` for minimal polynomials.

`IntegralRootNormalization` constructs an integral primitive generator by
multiplying the original root by the leading coefficient. It proves the
minimal-polynomial identity and the residue-root injection away from primes
dividing that coefficient. `IrreduciblePrimeLogBound` consequently proves the
sharp logarithmic bound for **every** integer polynomial irreducible over ℚ,
without requiring monicity or the no-fixed-prime condition. Convergence near
one is included in the theorem.

`HooleyExponentGap` defines
`e=(2^t−2^(t/q))/(q−1)−t/q` and proves `e≥t/(7q(q−1))>0` for `t≥1`,
`q>2`, and `q≥2t`. `HooleyPowerMajorant` substitutes the proved prime bound
into the differential majorant, giving `K_q(σ−1)^(−1−e)` with an explicit
coefficient. Its constants `C,b` depend only on the polynomial and work
simultaneously for all eligible `t,q`. `HooleyIntegratedPowerBound` integrates
this to obtain `U(σ)≤U(b)+(K_q/e)(σ−1)^(−e)`.

`HooleyMomentRecovery` proves the exact inverse transformation and the
exponent identity `2^(t/q)+e(q−1)=2^t−t+t/q`.
`HooleyMomentOrderConstants` bounds the prime-error power uniformly in `q`
and proves `K_q/e≤7E q` for a constant `E` depending only on `Q,t,C`.
It also bounds the endpoint uniformly in `q`. `HooleyDirichletPowerBound`
therefore proves, with `K,b` independent of `q`,
`L_q(σ)≤(Kq)^q (σ−1)^(−(2^t−t+t/q))` for `q>2`, `q≥2t`, and `1<σ≤b`.

`HooleySquarefreeRankin` proves `Δ(n)^t≤2^t M_q(n)^(t/q)` and the finite
Rankin comparison at `σ=1+1/log(x)`, whose extra factor is `exp(1)`.
`HooleySquarefreePowerBound` supplies a cutoff independent of `q`.
`MomentOrderOptimization` chooses the integer
`q=ceil(a sqrt(u/log(u)))` and proves that
`(q log(Kq)+tu/q)/sqrt(u log(u))` tends to `a/2+t/a`.
Taking `a=sqrt(2t)` gives the sharp coefficient `sqrt(2t)`.
`HooleySquarefreeMean` thus proves, for every `t≥1` and `η>sqrt(2t)`,
`Σ_{n≤x, squarefree} Δ(n)^t ρ_Q(n)/n ≤ C (log x)^(2^t−t)
exp(η sqrt(log₂ x log₃ x))` for all sufficiently large `x`.

`RootCountSubpolynomial` proves `ρ_Q(n)≪n^ε` from uniform prime-power
root bounds. `PowerfulDecomposition` separates each positive integer into
coprime squarefree and powerful parts, and represents every powerful integer
as `a²b³` with an injective choice of the pair. `PowerfulSummability` uses
this representation and divisor bounds to prove convergence of
`Σ_{a powerful} τ(a)^t ρ_Q(a)/a`. `HooleyPowerfulComparison` then uses
coprime multiplication and finite-sum reindexing to bound the unrestricted
mean by this convergent constant times the squarefree mean.
`HooleyWeightedMean` establishes the full sharp bound for every `t≥1`.
`CorollaryFive` combines its `Q=X`, `t=1` case with the dyadic floor-sum
reduction, proving the original bound uniformly for every `D≥1`.

`PrimeReciprocalLogBound` converts the proved near-pole prime-series bound
into `Σ_{p≤z}1/p≤exp(1)(C+log log z)`. `TotientLogLogBound` splits the
prime divisors of `n≤x` at `log x`; the large-prime contribution is bounded
using `#primeFactors(n)≤log n/log 2`. The reciprocal totient is consequently
at most `exp(A+B log₃ x)`. `TotientSubexponential` proves that this is
absorbed into every positive margin in the Hooley exponential coefficient.
`HooleyTotientMean` combines the two estimates, and `CorollaryEight` proves
both inequalities from the paper uniformly for `1≤|a|≤x`.
`CorollaryNine` applies the same bound to the progression rearrangement,
uniformly for every positive dyadic cutoff and `1≤|a|≤x`. The paper leaves
the residue range implicit in Corollary 9; this interface retains the range
from Corollary 8, and in particular covers every fixed nonzero residue
eventually. The condition also excludes the diagonal prime `p=a`.

For the remaining sieve-product bound, `NumberFieldPrimeNormRoots` proves
the reverse correspondence: every prime-norm ideal supplies a residue root,
and maps to the residue field are determined by the generator when the prime
is coprime to the conductor exponent. Hence the root count equals the number
of prime-norm ideals at such primes. `IdealNormDirichlet` also supplies a
positive lower pole bound from the Dedekind residue. `FiniteGeometricProduct` and `IdealFiniteEulerBound` encode ideals by their
prime-factor multiplicities and bound finite norm sums by geometric products.
`PrimeIdealNormBounds` bounds the number of ideals above each rational prime
by the field degree. `PrimeIdealErrorBounds` bounds the higher-residue-degree
and quadratic Euler contributions by convergent reciprocal-square sums.
`PrimeIdealRootComparison` retains coefficient one on the degree-one root
sum, and `IdealRootEulerBound` passes the comparison to the full Dirichlet
series. Together with the positive Dedekind residue, this proves the sharp
lower logarithmic bound in `MinpolyPrimeLowerBound`.
`RootNormalizationEquality` proves the reverse residue-root comparison at
primes not dividing the leading coefficient; `IrreduciblePrimeLowerBound`
thus transfers the lower bound to the original polynomial.
`PrimeRootReciprocalLowerBound` takes `σ=1+1/log x` and controls the omitted
prime tail by the logarithmically weighted pole bound. It proves
`Σ_{p≤x}ρ_Q(p)/p≥log log x−C`. `IrreducibleSieveProduct` deduces
`∏_{p≤x}(1−ρ_Q(p)/p)≪1/log x`. Combining this with the full sharp Hooley mean
and the proved short-sum reduction gives `CorollaryFour`, with the original
logarithmic exponent `2^t−t−1` and subexponential coefficient `sqrt(2t)+o(1)`.

The completed analytic chain is:

1. §4, Lemma 1, (23)–(25): the corrected multivariable totient comparison
   needed in the main proof is proved, with uniform constants. The selected-prime
   comparison needed for Corollary 6 is also proved. The printed general lemma
   is false, as witnessed by the checked arithmetic counterexample.
2. §4, Lemma 2, (26): the smooth tail bound, with its exponential saving and
   uniformity. The root-vector specialization is proved, including the global
   moment comparison, prime-band comparison, final truncation, and convergence
   of the infinite tail. The totient-modified version and degree/discriminant
   uniformity are also proved. `lemmaTwo : LemmaTwo` additionally proves the
   general class-`M` statement under the original Section 4 hypotheses.
3. §4, Theorem 1: proved, including the four contributions, exhaustive
   decomposition, and construction of the factorization data for original families.
4. Corollaries 1–3 are proved, including their statements for original polynomials.
5. Corollaries 4–5, the full sharp weighted Hooley mean, and the
   irreducible-polynomial sieve Euler-product estimate are proved.
6. Corollary 6 is proved for a nonconstant restricted coordinate, including
   the original-family interface and all uniformity requirements. A checked
   counterexample shows why this extra condition is needed in the general interface.
7. Theorem 2 is proved as `theoremTwo : TheoremTwo`, with positive polynomial
   degree, arbitrary fixed `k > degree`, and no restriction on fixed prime
   divisors. The following steps are proved:
   - `DivisorWindowMoments` bounds the divisor-window count by Hooley's function
     and splits its sum at an arbitrary threshold.
   - `HooleyLogarithmicSaving` and `HooleyDivisorTail` prove that the contribution
     above `(log x)^η` is `o(y)` for every `η > log 4 - 1`, using Corollary 4.
   - `CompleteResidueBlock` and `PolynomialDivisorWindowCount` lower-bound the
     total window count by `(y/2) Σ_{y/2<d≤y} ρ_Q(d)/d`.
   - `DivisorHitFixedPrime` combines the unrestricted tail estimates with the
     positive root-density lower bound from `IrreducibleRootDensity`.
   - `RoughCofactorBounds`, `RoughLogMass`, and `GreatestPrimeFactorCount` prove
     that rough cofactors have at most `k-1` prime factors, and at most `k-2`
     when a divisor lies in the window. Their logarithmic mass is bounded using
     the actual greatest prime factor of the product.
   - `ScalarPrimeSplit` constructs the smooth and rough parts at a real cutoff.
     `PrimeFactorLogGain` and `ScalarRoughLogMass` convert a quantitative lower
     mass estimate into an exponential gain from divisor hits.
     `GreatestPrimeFactorExponent` supplies the final strict exponent comparison
     for every `α < 2 - log 4`.
   - `PrimitiveResidueRoots`, `AffinePolynomialContent`, and `AffineNoFixedPrime`
     prove that every restriction modulo `degree! * |discriminant|`, after taking
     its primitive part, has no fixed prime divisor. At each small prime the
     discriminant bounds the content and forces reduction degree at most one;
     primes above the original degree are handled by primitivity.
   - `AffineIrreducibility` proves rational irreducibility of all these primitive
     restrictions. `HooleyFixedFactor` proves the Hooley multiplication bound
     without coprimality; `HooleyAffineReduction` reindexes and bounds the original
     short sum by the finite collection of primitive sums.
   - `AffineIntervalRange`, `HooleyCoarseLogBound`, and `HooleyFixedPrimeBound`
     transfer the moment estimate with any positive logarithmic exponent margin
     to every rationally irreducible polynomial, for `x^α ≤ y ≤ x/2`.
     `HooleyFixedPrimeTail` proves the required negligible large-window tail.
   - `DivisorHitFixedPrime` and `TheoremTwoDivisorHits` give the root-density-to-hit
     implication without a fixed-prime restriction, including the exact interval
     `y=x^(degree/k)` and the original integral irreducibility hypotheses.
     `exists_theoremTwo_divisorHit_bound` now discharges the root-density
     hypothesis and gives the unconditional lower bound.
   - `PolynomialLogMass` and `PolynomialLogMassLength` prove the total-logarithm
     lower bound `degree*y*log(x) - O_Q(y)` for every fixed positive interval
     exponent. `ShortIntervalCardinality` keeps the floor errors explicit.
   - `SmoothLogExpansion` and `PrimePowerLogExpansion` give exact finite sums
     for the logarithms of the canonical smooth parts, first by prime
     multiplicities and then by prime-power divisibility counts.
     `PolynomialLogParts` connects these sums to the original total logarithm
     and rough logarithmic mass; its convention at zeros leaves logarithms unchanged.
   - `ShortIntervalCongruenceUpper` and `SmoothLogRootBound` bound the smooth
     mass by `(y+1)*smoothLogRootMain + smoothLogRootError`.
     `PrimePowerLogCutoff` constructs the exponent cutoff from a bound on the
     values and bounds the remainder by `K*pi(z)*log(N)` when prime-power
     root counts are at most `K`.
   - `PrimitivePrimePowerRoots` proves uniform root bounds at every prime power
     for primitive polynomials with nonzero discriminant, including fixed primes.
     `SmoothLogCountingError` uses Chebyshev's prime-counting bound to give an
     `O(y)` remainder for cutoff `Cy`, value bound `A*x^g`, and `y ≥ x^β`.
   - `SmoothLogHigherPowers` proves that all higher-prime-power main terms
     contribute a bounded amount. `PolynomialSmoothPrimeBound` constructs the
     value-size bound and proves, with fixed constants,
     `polynomialSmoothLogMass ≤ (y+1)*primeRootLogSum(Q,Cy) + B*y`.
   - `IdealNormMultiplicative` proves the unique decomposition of an ideal of
     norm `m*n` into ideals of norms `m` and `n` when the norms are coprime.
     `IdealNormMean` packages these counts as a multiplicative arithmetic
     function with mean equal to the positive Dedekind zeta residue.
   - `ConvolutionMean` proves the exact summatory convolution identity and
     transfers a linear mean through any correction `g` with
     `Σ |g(d)|/d < ∞`. `DyadicMeanDensity` turns a positive linear mean
     of a nonnegative root-count minorant into a uniform dyadic lower bound.
   - `MultiplicativeCompletion` proves that Dirichlet inversion preserves
     multiplicativity. `RootIdealCorrection` constructs the correction for
     the squarefree-root minorant, proves its convolution identity with ideal
     counts, and proves cancellation at primes coprime to the conductor exponent.
   - `IdealPrimePowerCountBound` bounds `a_K(p^k)` by `(k+1)^[K:ℚ]` using
     an injective encoding by prime-ideal multiplicities. `DirichletInverseGrowth`
     and `RootIdealCorrectionGrowth` give uniform exponential local bounds.
     `RootIdealCorrectionTail` proves a summable `O(1/p²)` bound for the entire
     positive-exponent correction at sufficiently large good primes.
   - `PrimeIdealSupport` and `IdealMultiplicityVectors` identify ideals of
     norm `p^k` exactly with weighted multiplicity vectors over primes above `p`.
     `WeightedGeometricPolynomial` counts these vectors by coefficients of finite
     geometric products. `IdealLocalEulerPolynomial` proves that the local ideal
     series has inverse `∏_{P|p}(1-X^f(P))`.
   - `RootIdealLocalPolynomial` identifies every local correction with the
     polynomial `(1+ρ_Q(p)X)∏_{P|p}(1-X^f(P))`, proves its absolute summability,
     and proves positivity at `X=1/p`, including all exceptional primes.
     `EulerSummabilityCriterion` supplies the general convergence criterion.
     `RootIdealCorrectionPositive` proves positivity assuming absolute convergence.
   - `RootDensityFromIdealCounts` and `IrreducibleRootDensity` use eventual
     prime-root agreement under integral
     normalization to prove the positive mean and dyadic density for the original
     irreducible polynomial, with no fixed-prime restriction.
   - `PrimeIdealResidueDegree` bounds the total residue degree above each prime.
     `ArithmeticLogDerivative`, `PowerSeriesEulerDerivative`, and
     `GeometricEulerDerivative` construct and compute the ideal von Mangoldt
     function. `IdealVonMangoldtLocal` proves its exact local coefficients;
     `ArithmeticLogDerivativeSupport` proves prime-power support using a
     square-zero extension. `IdealVonMangoldtBounds` proves nonnegativity and
     the linear summatory Chebyshev estimate.
   - `IrreduciblePrimeIdealMatch` isolates eventual prime-count agreement.
     `PrimeRootMangoldtBound` bounds the weighted prime-root sum by the ideal
     reciprocal von Mangoldt sum plus a fixed exceptional-prime constant.
   - `SummatoryAbel`, `SummatoryFractionalMoment`, `ConvolutionPowerError`, and
     `LogWeightedSummatoryBound` supply the quantitative partial-summation steps.
     `IdealMangoldtMertensReduction` proves the sharp `log(x)+O(1)` upper bound
     conditional on `A_K(t)=κ_K*t+O(t^θ)` for some `0≤θ<1`. This power-saving
     ideal-count hypothesis is now supplied by `IdealNormPowerError`.
   - `LipschitzCubeCover`, `IntegerLatticeBallBound`, and `LatticePointsNearChart`
     give explicit mesh covers and an `O(t^m)` bound for lattice points near a
     dilated `m`-parameter chart. `IntegerLatticeCells` and `IntegerLatticeBoundary`
     compare lattice counts with volume using mixed unit cells.
     `LipschitzBoundaryLatticeCount` proves the general `O(t^m)` discrepancy
     theorem for bounded sets covered by finitely many Lipschitz boundary charts.
   - `NormLeOneBoundaryRadii` isolates radial and unit-coordinate faces of the
     number-field norm-one region. `MixedPolarCoordinates` supplies signs and
     compact angles; `NormLeOneRadialCharts` proves the full parametrizations
     are smooth. `CubeFaces` and `NormLeOneBoundaryCharts` produce finitely many
     smooth charts with `degree-1` parameters and prove the quantitative lattice
     count after any real linear coordinate change.
   - `LatticeCoordinateCount` identifies the count in an arbitrary integral
     basis with the integer-coordinate count. `NormConeLatticePowerError`
     converts a norm cutoff `x` to dilation by `x^(1/degree)` and proves error
     `O(x^((degree-1)/degree))` for a full lattice in the fundamental cone.
   - `IdealClassPowerError` transfers the lattice count to principal ideals
     divisible by an ideal and then to each ideal class, retaining the torsion
     multiplicity and norm scaling. `IdealNormPowerError` sums over the finite
     class group; `PowerErrorMean` identifies the leading coefficient with the
     established Dedekind residue.
   - `PrimeRootMertens` proves the unconditional weighted prime-root upper bound
     `log(x)+O(1)`. `PolynomialSmoothLogEstimate` and `TheoremTwoRoughMass`
     establish the small-prime and rough mass estimates with `O(y)` errors.
     `TheoremTwoValueBounds` supplies fixed cutoff constants, and
     `TheoremTwoLogGain` absorbs the error by divisor hits and retains the strict
     exponent margin. `TheoremTwo` assembles the original statement.

8. Theorem 3 and Corollaries 7–10 are proved. Corollaries 8–9 include
   the sharp asymptotic bound uniformly for `1≤|a|≤x`.

All fifteen numbered results are accounted for: Theorems 1–3, Corollaries 1–10,
and Lemma 2 have proofs with the scope and corrections recorded above; the
printed Lemma 1 is refuted and the needed replacements are proved. No result
has been substituted by an axiom or a structure field containing the desired
conclusion. The full build and audit check 3,039 declarations and allow only
`propext`, `Classical.choice`, and `Quot.sound`.


## Palomar statement surface

`Challenge.lean` restates Theorems 1–3, Corollaries 1–10, and Lemma 2 with only
Mathlib imports, concrete definitions, and fourteen deliberate theorem holes.
`Solution.lean` proves definitionally identical wrappers in
`NairTenenbaum.Submission`, and `comparator.json` lists the fourteen names. The source corrections in the proof map remain explicit
in the Challenge and the v0.4 `formalization.yaml`. The earlier machine-readable
progress inventory is preserved as `docs/completion-audit.yaml`.
Both modules compile. `scripts/CheckStatements.lean` checks exact agreement of
all fourteen compiled theorem types and their 19,610 transitive statement
constants, including generated helpers. `scripts/CheckAxioms.lean` additionally checks that every configured
name is a theorem with only the permitted axioms and that Solution does not
import Challenge. `scripts/check-submission.py` checks the local source layout,
size limits, dependency pins, and agreement between metadata and declarations.
The refactored working tree passed the full sandboxed Comparator check via
`scripts/verify-comparator.sh` on 2026-10-30, using host permissions for Bubblewrap's
namespace sandbox. The con-ron, NanoDa, and Lean default kernels all accepted the
exported solution. CI runs the same script. The submission is not yet registered,
and no immutable public snapshot has been verified here.
