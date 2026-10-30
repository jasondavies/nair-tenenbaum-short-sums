module

public import NairTenenbaum.RootIdealCorrectionPositive
public import NairTenenbaum.DyadicMeanDensity
public import NairTenenbaum.ConductorNonzero

@[expose] public section

/-! # Positive mean and dyadic density for minimal-polynomial roots

For an integral primitive generator, the squarefree-root counting function has
positive mean. This supplies a uniform lower bound for the dyadic root density.
-/

namespace NairTenenbaum

open Filter NumberField Polynomial
open scoped Topology

variable {K : Type*} [Field K] [NumberField K]

theorem exists_minpoly_squarefreeRoot_mean (θ : 𝓞 K)
    (hθ : RingOfIntegers.exponent θ ≠ 0) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun x : ℝ => arithmeticSummatory (squarefreeRootArithmetic (minpoly ℤ θ)) x / x)
        atTop (𝓝 L) := by
  let L : ℝ := dedekindZeta_residue K *
    ∑' n : ℕ, rootIdealCorrection K (minpoly ℤ θ) n / n
  refine ⟨L, mul_pos (dedekindZeta_residue_pos K) (rootIdealCorrection_minpoly_sum_pos K θ hθ), ?_⟩
  have H := idealNormArithmetic_convolution_mean K
    (rootIdealCorrection_minpoly_abs_summable K θ hθ)
  rw [rootIdealCorrection_mul_idealNorm] at H
  exact H

theorem exists_minpoly_dyadicRootDensity_lower_bound (θ : 𝓞 K)
    (hθ : RingOfIntegers.exponent θ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop, c ≤ dyadicRootDensitySum (minpoly ℤ θ) y := by
  obtain ⟨L, hL, hmean⟩ := exists_minpoly_squarefreeRoot_mean θ hθ
  exact ⟨L / 4, by positivity,
    eventually_dyadicRootDensity_ge_of_minorant_mean
      (squarefreeRootArithmetic_nonneg _) (squarefreeRootArithmetic_le_rootCount _) hL hmean⟩

theorem exists_generator_dyadicRootDensity_lower_bound (θ : 𝓞 K) (B : PowerBasis ℚ K)
    (hB : B.gen = (θ : K)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop, c ≤ dyadicRootDensitySum (minpoly ℤ θ) y :=
  exists_minpoly_dyadicRootDensity_lower_bound θ (conductor_exponent_ne_zero θ B hB)

end NairTenenbaum
