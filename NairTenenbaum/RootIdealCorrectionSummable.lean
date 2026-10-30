module

public import NairTenenbaum.RootIdealLocalPolynomial
public import NairTenenbaum.RootIdealCorrectionTail
public import NairTenenbaum.EulerSummabilityCriterion

@[expose] public section

/-! # Global absolute convergence of the root/ideal correction -/

namespace NairTenenbaum

open Filter NumberField Polynomial

variable (K : Type*) [Field K] [NumberField K]

theorem rootIdealCorrection_minpoly_prime_tails_summable (θ : 𝓞 K)
    (hθ : RingOfIntegers.exponent θ ≠ 0) :
    Summable (fun p : ℕ => if p.Prime then
      ∑' k : ℕ, |rootIdealCorrection K (minpoly ℤ θ) (p ^ (k + 1))| / (p : ℝ) ^ (k + 1)
      else 0) := by
  apply (summable_congr_atTop (g₁ := fun p : ℕ =>
    if p.Prime ∧ 2 * rootIdealCorrectionGrowthConstant K (minpoly ℤ θ) ≤ p ∧
        p.Coprime (RingOfIntegers.exponent θ) then
      ∑' k : ℕ, |rootIdealCorrection K (minpoly ℤ θ) (p ^ (k + 1))| / (p : ℝ) ^ (k + 1)
    else 0) ?_).mpr (rootIdealCorrection_minpoly_goodPrime_tail_summable K θ)
  filter_upwards [eventually_ge_atTop ⌈2 * rootIdealCorrectionGrowthConstant K (minpoly ℤ θ)⌉₊,
    eventually_gt_atTop (RingOfIntegers.exponent θ)] with p hpbound hpexp
  have hlarge : 2 * rootIdealCorrectionGrowthConstant K (minpoly ℤ θ) ≤ p :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpbound)
  by_cases hp : p.Prime
  · have hc : p.Coprime (RingOfIntegers.exponent θ) := hp.coprime_iff_not_dvd.mpr
      (fun hd => (not_le_of_gt hpexp) (Nat.le_of_dvd (Nat.pos_of_ne_zero hθ) hd))
    simp only [hp, hlarge, true_and, ite_true]
    rw [ite_eq_left hc]
  · simp [hp]

theorem rootIdealCorrection_minpoly_abs_summable (θ : 𝓞 K)
    (hθ : RingOfIntegers.exponent θ ≠ 0) :
    Summable (fun n : ℕ => |rootIdealCorrection K (minpoly ℤ θ) n| / n) := by
  apply summable_multiplicative_of_local_tails
  · intro n
    exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  · simp [(rootIdealCorrection_isMultiplicative K (minpoly ℤ θ)).1]
  · intro m n hcop
    rw [(rootIdealCorrection_isMultiplicative K (minpoly ℤ θ)).2 hcop, abs_mul, Nat.cast_mul,
      mul_div_mul_comm]
  · intro p hp
    simpa only [Nat.cast_pow] using rootIdealCorrection_local_abs_summable K (minpoly ℤ θ) hp
  · simpa only [Nat.cast_pow] using rootIdealCorrection_minpoly_prime_tails_summable K θ hθ

end NairTenenbaum
