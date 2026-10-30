module

public import NairTenenbaum.HooleyTotientMean
public import NairTenenbaum.HooleyPrimeShortSum

@[expose] public section

/-! # Corollary 8: Hooley's function at shifted primes

Both inequalities in the paper hold with constants uniform for `1≤|a|≤x`.
The asymptotic exponent is expressed by every coefficient greater than `sqrt(2)`.
-/

namespace NairTenenbaum

open Real Polynomial

def CorollaryEight : Prop :=
  ∀ ε η : ℝ, 0 < ε → ε < 1 → Real.sqrt 2 < η →
    ∃ x₀ C D : ℝ, 1 < x₀ ∧ 0 < C ∧ 0 < D ∧ ∀ a : ℤ, a ≠ 0 → ∀ x y : ℝ,
      x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ ε ≤ y → y ≤ x →
        hooleyPrimeSum a 1 x y ≤ C *
          (((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
            hooleyRootSum (X : ℤ[X]) 1 x) ∧
        ((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
            hooleyRootSum (X : ℤ[X]) 1 x ≤ D * (y / Real.log x * hooleySubexponential η x)

theorem corollaryEight : CorollaryEight := by
  intro ε η hε _ hη
  obtain ⟨x₁, C, _, hC, H⟩ := exists_hooleyPrimeSum_root_bound_uniform_shift hε (t := 1) zero_lt_one
  obtain ⟨x₂, D, hx₂, hD, HD⟩ := exists_totient_hooleyRootSum_sharp_bound hη
  refine ⟨max x₁ x₂, C, D, hx₂.trans_le (le_max_right _ _), hC, hD,
    fun a ha x y hx hax hy hyx => ?_⟩
  have hx₂' := (le_max_right x₁ x₂).trans_lt hx
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) ε).trans hy
  exact ⟨H a ha x y ((le_max_left _ _).trans_lt hx) hax hy hyx,
    HD x hx₂' a.natAbs (Int.natAbs_ne_zero.mpr ha) hax y hy₀⟩

theorem exists_hooleyPrimeSum_sharp_bound {ε η : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (hη : Real.sqrt 2 < η) :
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ a : ℤ, a ≠ 0 → ∀ x y : ℝ,
      x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ ε ≤ y → y ≤ x →
        hooleyPrimeSum a 1 x y ≤ C * (y / Real.log x * hooleySubexponential η x) := by
  obtain ⟨x₀, C, D, hx₀, hC, hD, H⟩ := corollaryEight ε η hε hε₁ hη
  refine ⟨x₀, C * D, hx₀, mul_pos hC hD, fun a ha x y hx hax hy hyx => ?_⟩
  obtain ⟨H₁, H₂⟩ := H a ha x y hx hax hy hyx
  exact H₁.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H₂ hC.le)

end NairTenenbaum
