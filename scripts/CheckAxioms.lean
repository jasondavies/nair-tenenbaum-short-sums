module

import all NairTenenbaum
import all Solution
import all NairTenenbaum.Arithmetic.Arithmetic
import all NairTenenbaum.Arithmetic.AuxiliaryFunctions
import all NairTenenbaum.Arithmetic.AuxiliarySeries
import all NairTenenbaum.Arithmetic.CongruenceCount
import all NairTenenbaum.Arithmetic.DivisorBounds
import all NairTenenbaum.Hooley.Hooley
import all NairTenenbaum.Polynomials.LinearCase
import all NairTenenbaum.Arithmetic.MinimalMajorant
import all NairTenenbaum.Arithmetic.Normalization
import all NairTenenbaum.Polynomials.PolynomialSystem
import all NairTenenbaum.Polynomials.PolynomialStructure
import all NairTenenbaum.Polynomials.PolynomialHeight
import all NairTenenbaum.Arithmetic.PrimePowerRoots
import all NairTenenbaum.Polynomials.DiscriminantBezout
import all NairTenenbaum.Sieve.BadPrimeRoots
import all NairTenenbaum.Polynomials.PolynomialLocal
import all NairTenenbaum.Arithmetic.UnitaryComparison
import all NairTenenbaum.Arithmetic.ComparisonKernel
import all NairTenenbaum.Arithmetic.TupleComparison
import all NairTenenbaum.Arithmetic.WeightTruncation
import all NairTenenbaum.Arithmetic.MultivariableComparison
import all NairTenenbaum.Arithmetic.ComparisonUniformity
import all NairTenenbaum.Arithmetic.ScalarComparison
import all NairTenenbaum.Arithmetic.ComparisonLocal
import all NairTenenbaum.Arithmetic.TotientTwist
import all NairTenenbaum.Arithmetic.PrimeLogSums
import all NairTenenbaum.Smooth.TiltedAuxiliary
import all NairTenenbaum.Smooth.MomentPrimeBounds
import all NairTenenbaum.Arithmetic.RootAuxiliary
import all NairTenenbaum.Counterexamples.PrimeSupportedFunction
import all NairTenenbaum.Counterexamples.LemmaOneCounterexample
import all NairTenenbaum.Counterexamples.LemmaOneObstruction
import all NairTenenbaum.Arithmetic.PrimeMajorant
import all NairTenenbaum.Arithmetic.PrimeSplitting
import all NairTenenbaum.Polynomials.RootCount
import all NairTenenbaum.Results.Targets
import all NairTenenbaum.Arithmetic.Weights
import all NairTenenbaum.Arithmetic.PrimePowerComparison
import all NairTenenbaum.Smooth.MomentKernel
import all NairTenenbaum.Smooth.SmoothMoment
import all NairTenenbaum.Smooth.SmoothWeightSum
import all NairTenenbaum.Smooth.PrimeBandBounds
import all NairTenenbaum.Smooth.SmoothCutoffComparison
import all NairTenenbaum.Smooth.SmoothTruncation
import all NairTenenbaum.Smooth.SmoothTruncationUniform
import all NairTenenbaum.Smooth.RootSmoothTail
import all NairTenenbaum.Smooth.TiltedTotientComparison
import all NairTenenbaum.Smooth.TotientSmoothTail
import all NairTenenbaum.Smooth.SmoothTailUniformity
import all NairTenenbaum.Polynomials.DiscriminantSplitting
import all NairTenenbaum.Arithmetic.PrimeThreshold
import all NairTenenbaum.Arithmetic.FractionalAuxiliary
import all NairTenenbaum.Sieve.BadPrimeMass
import all NairTenenbaum.Sieve.JointCongruence
import all NairTenenbaum.Sieve.BadPrimeCongruence
import all NairTenenbaum.Sieve.SelbergWeights
import all NairTenenbaum.Sieve.SelbergDenominator
import all NairTenenbaum.Sieve.SelbergCoefficientBounds
import all NairTenenbaum.Arithmetic.PrimeFactorBounds
import all NairTenenbaum.Sieve.SelbergRemainder
import all NairTenenbaum.Polynomials.PolynomialSieve
import all NairTenenbaum.Sieve.ConditionalPolynomialSieve
import all NairTenenbaum.Sieve.OmittedEulerFactors
import all NairTenenbaum.Sieve.SievePrimes
import all NairTenenbaum.Sieve.SieveProductLowerBound
import all NairTenenbaum.Sieve.SieveLevel
import all NairTenenbaum.Arithmetic.TotientProducts
import all NairTenenbaum.Sieve.BadPrimeSieve
import all NairTenenbaum.Sieve.SmallDivisorSieve
import all NairTenenbaum.Sieve.SiftedDivisorSplit
import all NairTenenbaum.Sieve.SmallDivisorSum
import all NairTenenbaum.Sieve.SieveScales
import all NairTenenbaum.Sieve.SieveCutoffComparison
import all NairTenenbaum.Sieve.SmallDivisorMainTerm
import all NairTenenbaum.Arithmetic.RoughMass
import all NairTenenbaum.Polynomials.PolynomialValueBounds
import all NairTenenbaum.Polynomials.PolynomialValueTuples
import all NairTenenbaum.Sieve.SmallDivisorMajorant
import all NairTenenbaum.Contributions.RealIntervalBounds
import all NairTenenbaum.Contributions.FirstContribution
import all NairTenenbaum.Contributions.FirstContributionReal
import all NairTenenbaum.Arithmetic.PrimePowerThreshold
import all NairTenenbaum.Arithmetic.PrimePowerCounting
import all NairTenenbaum.Arithmetic.ValueWeightBounds
import all NairTenenbaum.Contributions.SecondContributionCounting
import all NairTenenbaum.Contributions.SecondContributionWeights
import all NairTenenbaum.Contributions.SecondContribution
import all NairTenenbaum.Smooth.SmoothDivisorDensity
import all NairTenenbaum.Smooth.SmoothDivisorCounting
import all NairTenenbaum.Contributions.ThirdContributionWeights
import all NairTenenbaum.Contributions.ThirdContribution
import all NairTenenbaum.Smooth.SmoothMomentUniformity
import all NairTenenbaum.Sieve.BadPrimeMoments
import all NairTenenbaum.Smooth.SplitSmoothTail
import all NairTenenbaum.Smooth.SmoothTailSieveReindex
import all NairTenenbaum.Smooth.SmoothTailSieve
import all NairTenenbaum.Arithmetic.MainTermLowerBound
import all NairTenenbaum.Smooth.LargePrefixScales

import all NairTenenbaum.Smooth.SmoothTailMajorant

import all NairTenenbaum.Smooth.PrimeBandDecay

import all NairTenenbaum.Smooth.PrimeBandMajorant

import all NairTenenbaum.Smooth.PrimeBandContribution

import all NairTenenbaum.Smooth.PrimeBandSummation

import all NairTenenbaum.Smooth.PrimeBandCutoff

import all NairTenenbaum.Smooth.PrimeBandCover


import all NairTenenbaum.Contributions.IntermediateContributionReal

import all NairTenenbaum.Smooth.LargePrefixMainTerm



import all NairTenenbaum.Contributions.ShortSumDecomposition

import all NairTenenbaum.Results.TheoremOne

import all NairTenenbaum.Progressions.AffineRootCounts

import all NairTenenbaum.Progressions.AffinePolynomialSystem

import all NairTenenbaum.Progressions.AffineDiscriminant

import all NairTenenbaum.Progressions.AffineBadDiscriminant

import all NairTenenbaum.Progressions.AffineWeights


import all NairTenenbaum.Contributions.ValueBoundContributions

import all NairTenenbaum.Contributions.IntegerIntervalDecomposition

import all NairTenenbaum.Contributions.IntegerIntervalBound

import all NairTenenbaum.Progressions.ProgressionIntervals

import all NairTenenbaum.Progressions.ProgressionBound

import all NairTenenbaum.Results.CorollaryOne

import all NairTenenbaum.Polynomials.IrreducibleSystem

import all NairTenenbaum.Polynomials.IrreducibleProgressionWeights

import all NairTenenbaum.Results.CorollaryTwo

import all NairTenenbaum.Arithmetic.ProductArithmetic

import all NairTenenbaum.Arithmetic.DivisorTupleDisjointness

import all NairTenenbaum.Sieve.JointDensityComparison

import all NairTenenbaum.Polynomials.SubstitutionDensity

import all NairTenenbaum.Arithmetic.FactoredWeightBound

import all NairTenenbaum.Results.CorollaryThree

import all NairTenenbaum.Polynomials.FamilyFactorization

import all NairTenenbaum.Results.FamilyTheorems

import all NairTenenbaum.PrimeArguments.PrimeArgumentRoots

import all NairTenenbaum.PrimeArguments.PrimeArgumentEuler

import all NairTenenbaum.Sieve.LocalConditionalSieve

import all NairTenenbaum.PrimeArguments.PrimeArgumentSieve

import all NairTenenbaum.Arithmetic.TotientComparisonExponents

import all NairTenenbaum.PrimeArguments.PrimeArgumentSieveLevel

import all NairTenenbaum.PrimeArguments.PrimeArgumentMajorant

import all NairTenenbaum.PrimeArguments.PrimeArgumentBadSieve

import all NairTenenbaum.PrimeArguments.PrimeArgumentSmallSieve

import all NairTenenbaum.PrimeArguments.PrimeArgumentSmallSum

import all NairTenenbaum.PrimeArguments.PrimeArgumentScales

import all NairTenenbaum.PrimeArguments.PrimeArgumentMainTerm

import all NairTenenbaum.PrimeArguments.PrimeArgumentFirstContribution

import all NairTenenbaum.PrimeArguments.PrimeArgumentMoment

import all NairTenenbaum.PrimeArguments.PrimeArgumentSplitTail

import all NairTenenbaum.PrimeArguments.PrimeArgumentTailReindex

import all NairTenenbaum.PrimeArguments.PrimeArgumentTailSieve

import all NairTenenbaum.PrimeArguments.PrimeArgumentBand

import all NairTenenbaum.PrimeArguments.PrimeArgumentTailMajorant

import all NairTenenbaum.PrimeArguments.PrimeArgumentBandContribution

import all NairTenenbaum.PrimeArguments.PrimeArgumentBands

import all NairTenenbaum.PrimeArguments.PrimeArgumentCover

import all NairTenenbaum.PrimeArguments.PrimeArgumentExceptional

import all NairTenenbaum.PrimeArguments.PrimeArgumentDecomposition

import all NairTenenbaum.PrimeArguments.PrimeArgumentIntervalBound

import all NairTenenbaum.PrimeArguments.PrimeArgumentHeight

import all NairTenenbaum.PrimeArguments.PrimeShortSum

import all NairTenenbaum.Results.TheoremThree

import all NairTenenbaum.Results.PrimeFamilyTheorem

import all NairTenenbaum.Polynomials.ShiftedLinearSystem

import all NairTenenbaum.Results.CorollarySeven

import all NairTenenbaum.DivisorSums.GoldbachSieve

import all NairTenenbaum.DivisorSums.GoldbachScales

import all NairTenenbaum.Results.CorollaryTen

import all NairTenenbaum.Smooth.SelectedMoment

import all NairTenenbaum.Smooth.SelectedTilt

import all NairTenenbaum.Smooth.SelectedTiltComparison

import all NairTenenbaum.Polynomials.PolynomialPreimages

import all NairTenenbaum.Arithmetic.FixedSmoothCounting

import all NairTenenbaum.Smooth.SmoothValueRankin

import all NairTenenbaum.Smooth.SmoothValueExceptional

import all NairTenenbaum.Smooth.SmoothValueScales

import all NairTenenbaum.Smooth.SmoothValuePowerBounds

import all NairTenenbaum.Smooth.SmoothTiltBound

import all NairTenenbaum.Results.CorollarySix

import all NairTenenbaum.Results.SmoothFamilyTheorem

import all NairTenenbaum.Counterexamples.ConstantCoordinate

import all NairTenenbaum.Counterexamples.CorollarySixObstruction

import all NairTenenbaum.Arithmetic.DivisorSumRearrangement

import all NairTenenbaum.Hooley.HooleyShortSum

import all NairTenenbaum.Arithmetic.PrimeProgressionRearrangement

import all NairTenenbaum.Hooley.HooleyPrimeShortSum

import all NairTenenbaum.Hooley.HooleyAverageReductions

import all NairTenenbaum.Hooley.HooleyMoments

import all NairTenenbaum.Hooley.HooleyMomentComparison

import all NairTenenbaum.Hooley.HooleyMomentRecurrence

import all NairTenenbaum.Hooley.HooleyMomentInterpolation

import all NairTenenbaum.Arithmetic.PrimeLogIntervals

import all NairTenenbaum.Hooley.HooleyPrimeSampling

import all NairTenenbaum.Hooley.HooleyPrimeMixedBound

import all NairTenenbaum.Hooley.HooleyWeightedPrimeStep

import all NairTenenbaum.Arithmetic.WeightedMomentPowers

import all NairTenenbaum.Hooley.HooleyDirichletCoefficients

import all NairTenenbaum.Hooley.HooleyDirichletSeries

import all NairTenenbaum.Hooley.HooleyDirichletDerivative

import all NairTenenbaum.Arithmetic.PrimeFactorReindex
import all NairTenenbaum.Hooley.HooleyDirichletPrimeExpansion
import all NairTenenbaum.Hooley.HooleyInfinitePrimeStep
import all NairTenenbaum.Arithmetic.SeriesInterpolation
import all NairTenenbaum.Hooley.HooleyDirichletError
import all NairTenenbaum.Hooley.HooleyDifferentialInequality

import all NairTenenbaum.Arithmetic.SquarefreeEulerBound
import all NairTenenbaum.Hooley.HooleyDivisorEulerBound
import all NairTenenbaum.Arithmetic.RootPrimeSeriesDerivative
import all NairTenenbaum.Arithmetic.DifferentialInterpolation
import all NairTenenbaum.Hooley.HooleyIntegratingFactor
import all NairTenenbaum.Hooley.HooleyIntegratedBound
import all NairTenenbaum.Arithmetic.PrimeDirichletPoleBound

import all NairTenenbaum.NumberFields.ResidueHomKernels
import all NairTenenbaum.NumberFields.ConductorQuotient
import all NairTenenbaum.NumberFields.NumberFieldResidueRoots
import all NairTenenbaum.NumberFields.IdealNormDirichlet
import all NairTenenbaum.NumberFields.ConductorNonzero
import all NairTenenbaum.NumberFields.MinpolyEulerProduct
import all NairTenenbaum.Arithmetic.PrimeProductLogBound
import all NairTenenbaum.NumberFields.MinpolyPrimeLogBound
import all NairTenenbaum.NumberFields.IntegralRootNormalization
import all NairTenenbaum.NumberFields.IrreduciblePrimeLogBound
import all NairTenenbaum.Hooley.HooleyExponentGap
import all NairTenenbaum.Hooley.HooleyPowerMajorant
import all NairTenenbaum.Hooley.HooleyIntegratedPowerBound

import all NairTenenbaum.Hooley.HooleyMomentRecovery
import all NairTenenbaum.Hooley.HooleyMomentOrderConstants
import all NairTenenbaum.Hooley.HooleyDirichletPowerBound
import all NairTenenbaum.Hooley.HooleySquarefreeRankin
import all NairTenenbaum.Hooley.HooleySquarefreePowerBound
import all NairTenenbaum.Smooth.MomentOrderOptimization
import all NairTenenbaum.Hooley.HooleySquarefreeMean

import all NairTenenbaum.Polynomials.RootCountSubpolynomial
import all NairTenenbaum.Arithmetic.PowerfulDecomposition
import all NairTenenbaum.Arithmetic.PowerfulSummability
import all NairTenenbaum.Hooley.HooleyPowerfulComparison
import all NairTenenbaum.Hooley.HooleyWeightedMean
import all NairTenenbaum.Results.CorollaryFive

import all NairTenenbaum.Arithmetic.PrimeReciprocalLogBound
import all NairTenenbaum.Arithmetic.TotientLogLogBound
import all NairTenenbaum.Arithmetic.TotientSubexponential
import all NairTenenbaum.Hooley.HooleyTotientMean
import all NairTenenbaum.Results.CorollaryEight
import all NairTenenbaum.Results.CorollaryNine

import all NairTenenbaum.NumberFields.NumberFieldPrimeNormRoots

import all NairTenenbaum.Arithmetic.FiniteGeometricProduct
import all NairTenenbaum.NumberFields.IdealFiniteEulerBound
import all NairTenenbaum.NumberFields.PrimeIdealNormBounds
import all NairTenenbaum.NumberFields.PrimeIdealErrorBounds
import all NairTenenbaum.NumberFields.PrimeIdealRootComparison
import all NairTenenbaum.NumberFields.IdealRootEulerBound
import all NairTenenbaum.NumberFields.MinpolyPrimeLowerBound
import all NairTenenbaum.NumberFields.RootNormalizationEquality
import all NairTenenbaum.NumberFields.IrreduciblePrimeLowerBound
import all NairTenenbaum.NumberFields.PrimeRootReciprocalLowerBound
import all NairTenenbaum.NumberFields.IrreducibleSieveProduct
import all NairTenenbaum.Results.CorollaryFour

import all NairTenenbaum.DivisorSums.DivisorWindowMoments
import all NairTenenbaum.Hooley.HooleyLogarithmicSaving
import all NairTenenbaum.Hooley.HooleyDivisorTail
import all NairTenenbaum.Arithmetic.CompleteResidueBlock
import all NairTenenbaum.DivisorSums.PolynomialDivisorWindowCount
import all NairTenenbaum.DivisorSums.RoughCofactorBounds
import all NairTenenbaum.DivisorSums.RoughLogMass
import all NairTenenbaum.DivisorSums.GreatestPrimeFactorCount
import all NairTenenbaum.DivisorSums.PrimeFactorLogGain
import all NairTenenbaum.Arithmetic.ScalarPrimeSplit
import all NairTenenbaum.Results.TheoremTwoStatement
import all NairTenenbaum.DivisorSums.ScalarRoughLogMass

import all NairTenenbaum.DivisorSums.GreatestPrimeFactorExponent

import all NairTenenbaum.Polynomials.PrimitiveResidueRoots
import all NairTenenbaum.Progressions.AffinePolynomialContent
import all NairTenenbaum.Progressions.AffineNoFixedPrime
import all NairTenenbaum.Progressions.AffineIrreducibility
import all NairTenenbaum.Hooley.HooleyFixedFactor
import all NairTenenbaum.Hooley.HooleyAffineReduction
import all NairTenenbaum.Progressions.AffineIntervalRange
import all NairTenenbaum.Hooley.HooleyCoarseLogBound
import all NairTenenbaum.Hooley.HooleyFixedPrimeBound
import all NairTenenbaum.Hooley.HooleyFixedPrimeTail
import all NairTenenbaum.DivisorSums.DivisorHitFixedPrime
import all NairTenenbaum.Results.TheoremTwoDivisorHits

import all NairTenenbaum.Polynomials.PolynomialLogMass
import all NairTenenbaum.Contributions.ShortIntervalCardinality
import all NairTenenbaum.Polynomials.PolynomialLogMassLength
import all NairTenenbaum.Smooth.SmoothLogExpansion
import all NairTenenbaum.Arithmetic.PrimePowerLogExpansion
import all NairTenenbaum.Polynomials.PolynomialLogParts
import all NairTenenbaum.Contributions.ShortIntervalCongruenceUpper
import all NairTenenbaum.Smooth.SmoothLogRootBound
import all NairTenenbaum.Arithmetic.PrimePowerLogCutoff

import all NairTenenbaum.Polynomials.PrimitivePrimePowerRoots
import all NairTenenbaum.Smooth.SmoothLogCountingError
import all NairTenenbaum.Smooth.SmoothLogHigherPowers
import all NairTenenbaum.Polynomials.PolynomialSmoothPrimeBound

import all NairTenenbaum.NumberFields.IdealNormMultiplicative
import all NairTenenbaum.NumberFields.ConvolutionMean

import all NairTenenbaum.NumberFields.IdealNormMean
import all NairTenenbaum.Arithmetic.DyadicMeanDensity

import all NairTenenbaum.Arithmetic.MultiplicativeCompletion
import all NairTenenbaum.NumberFields.RootIdealCorrection
import all NairTenenbaum.NumberFields.IdealPrimePowerCountBound
import all NairTenenbaum.NumberFields.DirichletInverseGrowth
import all NairTenenbaum.NumberFields.RootIdealCorrectionGrowth
import all NairTenenbaum.NumberFields.RootIdealCorrectionTail

import all NairTenenbaum.NumberFields.PrimeIdealSupport
import all NairTenenbaum.NumberFields.IdealMultiplicityVectors
import all NairTenenbaum.Arithmetic.WeightedGeometricPolynomial
import all NairTenenbaum.NumberFields.IdealLocalEulerPolynomial
import all NairTenenbaum.NumberFields.RootIdealLocalPolynomial
import all NairTenenbaum.NumberFields.EulerSummabilityCriterion
import all NairTenenbaum.NumberFields.RootIdealCorrectionPositive

import all NairTenenbaum.NumberFields.RootDensityFromIdealCounts
import all NairTenenbaum.NumberFields.IrreducibleRootDensity

import all NairTenenbaum.NumberFields.PrimeIdealResidueDegree
import all NairTenenbaum.NumberFields.ArithmeticLogDerivative
import all NairTenenbaum.NumberFields.PowerSeriesEulerDerivative
import all NairTenenbaum.NumberFields.GeometricEulerDerivative
import all NairTenenbaum.NumberFields.IdealVonMangoldtLocal
import all NairTenenbaum.NumberFields.ArithmeticLogDerivativeSupport
import all NairTenenbaum.NumberFields.IdealVonMangoldtBounds
import all NairTenenbaum.NumberFields.IrreduciblePrimeIdealMatch
import all NairTenenbaum.NumberFields.PrimeRootMangoldtBound

import all NairTenenbaum.Arithmetic.SummatoryAbel
import all NairTenenbaum.Arithmetic.SummatoryFractionalMoment
import all NairTenenbaum.NumberFields.ConvolutionPowerError
import all NairTenenbaum.NumberFields.LogWeightedSummatoryBound
import all NairTenenbaum.NumberFields.IdealMangoldtMertensReduction

import all NairTenenbaum.Geometry.LipschitzCubeCover
import all NairTenenbaum.Geometry.IntegerLatticeBallBound
import all NairTenenbaum.Geometry.LatticePointsNearChart
import all NairTenenbaum.Geometry.IntegerLatticeCells
import all NairTenenbaum.Geometry.IntegerLatticeBoundary
import all NairTenenbaum.Geometry.LipschitzBoundaryLatticeCount
import all NairTenenbaum.Geometry.NormLeOneBoundaryRadii
import all NairTenenbaum.Geometry.MixedPolarCoordinates
import all NairTenenbaum.Geometry.NormLeOneRadialCharts
import all NairTenenbaum.Geometry.CubeFaces
import all NairTenenbaum.Geometry.NormLeOneBoundaryCharts

import all NairTenenbaum.Geometry.LatticeCoordinateCount
import all NairTenenbaum.Geometry.NormConeLatticePowerError

import all NairTenenbaum.NumberFields.IdealClassPowerError
import all NairTenenbaum.NumberFields.IdealNormPowerError
import all NairTenenbaum.Polynomials.PolynomialSmoothLogEstimate
import all NairTenenbaum.NumberFields.PowerErrorMean
import all NairTenenbaum.NumberFields.PrimeRootMertens
import all NairTenenbaum.Results.TheoremTwo
import all NairTenenbaum.Results.TheoremTwoLogGain
import all NairTenenbaum.Results.TheoremTwoRoughMass
import all NairTenenbaum.Results.TheoremTwoValueBounds

import all NairTenenbaum.Arithmetic.FloorRootArithmetic
import all NairTenenbaum.Arithmetic.AppendArithmetic
import all NairTenenbaum.Smooth.LiftedWeights
import all NairTenenbaum.Smooth.LiftedWeightSums
import all NairTenenbaum.Smooth.GeneralSmoothTail
import all NairTenenbaum.Results.LemmaTwo
meta import Lean

/-! Run after `lake build`. All project declarations, including private and generated
ones, are checked by defining module rather than by declaration namespace.
An omitted source file is an error, so adding an unimported module cannot hide a proof hole.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let scriptDir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let root ← IO.FS.realPath (scriptDir / "..")
  let sourceRoot := root / "NairTenenbaum"
  for path in ← sourceRoot.walkDir do
    if path.extension == some "lean" then
      let parts := (path.withExtension "").components.drop sourceRoot.components.length
      let name := parts.foldl Name.str `NairTenenbaum
      unless env.header.imports.any (fun i => i.module == name && i.importAll) do
        throwError "Source module {name} must be imported with `import all` in this audit"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for name in env.header.moduleNames, data in env.header.moduleData do
    if (`NairTenenbaum).isPrefixOf name || name == `Solution then
      for decl in data.constNames do
        checked := checked + 1
        for ax in ← collectAxioms decl do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {decl} (module {name})"
  if checked == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Audited {checked} declarations; only propext, Classical.choice and Quot.sound found."
  if env.header.moduleNames.contains `Challenge then
    throwError "The solution must not import Challenge"
  let configText ← IO.FS.readFile (root / "comparator.json")
  let config ← match Json.parse configText with
    | .ok config => pure config
    | .error error => throwError "Invalid Comparator JSON: {error}"
  let names ← match config.getObjValAs? (Array String) "theorem_names" with
    | .ok names => pure names
    | .error error => throwError "Missing theorem_names: {error}"
  for text in names do
    let name := text.toName
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Submission declaration {name} is not a proved theorem"
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in submission theorem {name}"
  logInfo m!"Audited all {names.size} configured Solution theorems; no Challenge import or forbidden axioms."
