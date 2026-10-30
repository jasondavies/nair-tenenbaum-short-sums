module

public import NairTenenbaum.SecondContributionCounting
public import NairTenenbaum.ValueWeightBounds

@[expose] public section

/-! # Weighted power saving for the second-class exceptional set -/

namespace NairTenenbaum

noncomputable def PolynomialSystem.primePowerContribution {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (z : ℝ) (a b : ℤ) : ℝ :=
  ∑ t ∈ primePowerExceptionalSet P.R z (z ^ 3) a b,
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

/-- Combining the elementary count with the pointwise admissibility bound. -/
theorem PolynomialSystem.primePowerContribution_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    {x δ z : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) (hz : 1 ≤ z)
    (hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x) {a b : ℤ} (hab : a ≤ b)
    (hlevel : z ^ 4 ≤ (b : ℝ) - a)
    (hinterval : ∀ t ∈ Finset.Ioc a b, (t.natAbs : ℝ) ≤ 2 * x) :
    P.primePowerContribution F z a b ≤
      (4 * (P.total.natDegree : ℝ) * (max P.total.natDegree (P.badDiscriminant ^ 3) : ℕ) *
        (B * (((P.total.natDegree : ℝ) + 1) * 2 ^ P.total.natDegree) ^ σ)) *
        ((b : ℝ) - a) * (x ^ (((P.total.natDegree : ℝ) + 1 / δ) * σ) / z ^ 2) * F 1 := by
  let W := B * (((P.total.natDegree : ℝ) + 1) * 2 ^ P.total.natDegree) ^ σ *
    x ^ (((P.total.natDegree : ℝ) + 1 / δ) * σ) * F 1
  have hW : 0 ≤ W := by dsimp [W]; positivity [hF.nonneg 1]
  have H : P.primePowerContribution F z a b ≤
      ((primePowerExceptionalSet P.R z (z ^ 3) a b).card : ℝ) * W := by
    unfold primePowerContribution
    apply le_trans (Finset.sum_le_sum (fun t ht =>
      P.value_weight_le hF hB hσ hx hδ hheight (hinterval t (Finset.mem_filter.mp ht).1)))
    simp only [Finset.sum_const, nsmul_eq_mul, W, primePowerExceptionalSet, le_refl]
  apply H.trans
  have H' := mul_le_mul_of_nonneg_right (P.primePowerExceptionalSet_cube_card_le hz hab hlevel) hW
  dsimp only [W] at H'
  convert H' using 1
  ring

/-- Theorem 1's growth exponent leaves at least `ε/3` after the quadratic
prime-power saving, for every positive total degree. -/
theorem secondContribution_exponent {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ((g : ℝ) + 1 / δ) * (ε * δ / 3) - (g : ℝ) * ε ≤ -(ε / 3) := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have heq : ((g : ℝ) + 1 / δ) * (ε * δ / 3) = ((g : ℝ) * δ + 1) * ε / 3 := by
    field_simp
  rw [heq]
  have H : (g : ℝ) * δ ≤ g := mul_le_of_le_one_right (by positivity) hδ₁
  nlinarith [mul_le_mul_of_nonneg_right H hε, mul_le_mul_of_nonneg_right hg₁ hε]

theorem secondContribution_power_saving {g : ℕ} (hg : 0 < g) {ε δ x : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hx : 1 ≤ x) :
    x ^ (((g : ℝ) + 1 / δ) * (ε * δ / 3)) / (x ^ ((g : ℝ) * ε / 2)) ^ 2 ≤ x ^ (-(ε / 3)) := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heq : (x ^ ((g : ℝ) * ε / 2)) ^ 2 = x ^ ((g : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx₀.le]
    congr 1
    norm_num
  rw [heq, ← Real.rpow_sub hx₀]
  exact Real.rpow_le_rpow_of_exponent_le hx (secondContribution_exponent hg hε hδ hδ₁)

/-- The weighted exceptional sum has a uniform negative-power saving. -/
theorem PolynomialSystem.primePowerContribution_power_saving {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g) (hg : 0 < g)
    {A B ε δ x y : ℝ} {F : ArithmeticMap k} (hF : Admissible A B (ε * δ / 3) F)
    (hB : 0 ≤ B) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hx : 1 ≤ x)
    (hz : 1 ≤ x ^ ((g : ℝ) * ε / 2))
    (hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x) {a b : ℤ} (hab : a ≤ b)
    (hlevel : (x ^ ((g : ℝ) * ε / 2)) ^ 4 ≤ (b : ℝ) - a)
    (hlength : (b : ℝ) - a ≤ 2 * y)
    (hinterval : ∀ t ∈ Finset.Ioc a b, (t.natAbs : ℝ) ≤ 2 * x) :
    P.primePowerContribution F (x ^ ((g : ℝ) * ε / 2)) a b ≤
      (8 * (g : ℝ) * (max g (P.badDiscriminant ^ 3) : ℕ) *
        (B * (((g : ℝ) + 1) * 2 ^ g) ^ (ε * δ / 3))) * y * x ^ (-(ε / 3)) * F 1 := by
  have H := P.primePowerContribution_le hF hB (by positivity) hx hδ hz hheight hab hlevel hinterval
  rw [hdeg] at H
  let C := 4 * (g : ℝ) * (max g (P.badDiscriminant ^ 3) : ℕ) *
    (B * (((g : ℝ) + 1) * 2 ^ g) ^ (ε * δ / 3))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hy : 0 ≤ y := by linarith
  have H' := mul_le_mul hlength (secondContribution_power_saving hg hε.le hδ hδ₁ hx)
    (div_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _) (sq_nonneg _)) (by positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H' hC) (hF.nonneg 1)
  apply H.trans
  dsimp only [C] at H''
  convert H'' using 1 <;> ring

end NairTenenbaum
