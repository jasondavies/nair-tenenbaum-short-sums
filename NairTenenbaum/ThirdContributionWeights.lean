module

public import NairTenenbaum.SmoothDivisorCounting
public import NairTenenbaum.ValueWeightBounds

@[expose] public section

/-! # A power saving for large smooth divisor tuples -/

namespace NairTenenbaum

noncomputable def PolynomialSystem.smoothDivisorContribution {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (s : Finset ℕ) (N : ℕ+) (T : ℝ) (a b : ℤ) : ℝ :=
  ∑ t ∈ smoothDivisorExceptionalSet P.radical s N T a b,
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

theorem PolynomialSystem.smoothDivisorContribution_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    {x δ T : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) (hT : 0 < T)
    (hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x) (s : Finset ℕ) (N : ℕ+)
    {a b : ℤ} (hab : a ≤ b) (hlevel : (N : ℝ) ≤ (b : ℝ) - a)
    (hinterval : ∀ t ∈ Finset.Ioc a b, (t.natAbs : ℝ) ≤ 2 * x) :
    P.smoothDivisorContribution F s N T a b ≤
      (2 * smoothDivisorBound P.total.natDegree P.badDiscriminant s *
        (B * (((P.total.natDegree : ℝ) + 1) * 2 ^ P.total.natDegree) ^ σ)) *
        ((b : ℝ) - a) * (x ^ (((P.total.natDegree : ℝ) + 1 / δ) * σ) * T ^ (-(1 / 2 : ℝ))) * F 1 := by
  let W := B * (((P.total.natDegree : ℝ) + 1) * 2 ^ P.total.natDegree) ^ σ *
    x ^ (((P.total.natDegree : ℝ) + 1 / δ) * σ) * F 1
  have hW : 0 ≤ W := by dsimp [W]; positivity [hF.nonneg 1]
  have H : P.smoothDivisorContribution F s N T a b ≤
      ((smoothDivisorExceptionalSet P.radical s N T a b).card : ℝ) * W := by
    unfold smoothDivisorContribution
    apply le_trans (Finset.sum_le_sum (fun t ht => P.value_weight_le hF hB hσ hx hδ hheight
      (hinterval t (Finset.mem_filter.mp ht).1)))
    simp only [Finset.sum_const, nsmul_eq_mul, W, smoothDivisorExceptionalSet, le_refl]
  apply H.trans
  have H' := mul_le_mul_of_nonneg_right (P.smoothDivisorExceptionalSet_card_le s N hT hab hlevel) hW
  dsimp only [W] at H'
  convert H' using 1
  ring

/-- The square-root density saving leaves a uniform gap, including degree one. -/
theorem thirdContribution_exponent {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ((g : ℝ) + 1 / δ) * (ε * δ / 3) - 3 * (g : ℝ) * ε / 4 ≤ -(ε / 12) := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have heq : ((g : ℝ) + 1 / δ) * (ε * δ / 3) = ((g : ℝ) * δ + 1) * ε / 3 := by field_simp
  rw [heq]
  have H : (g : ℝ) * δ ≤ g := mul_le_of_le_one_right (by positivity) hδ₁
  nlinarith [mul_le_mul_of_nonneg_right H hε, mul_le_mul_of_nonneg_right hg₁ hε]

theorem thirdContribution_power_saving {g : ℕ} (hg : 0 < g) {ε δ x : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hx : 1 ≤ x) :
    x ^ (((g : ℝ) + 1 / δ) * (ε * δ / 3)) *
      (x ^ (3 * (g : ℝ) * ε / 2)) ^ (-(1 / 2 : ℝ)) ≤ x ^ (-(ε / 12)) := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [← Real.rpow_mul hx₀.le, ← Real.rpow_add hx₀]
  apply Real.rpow_le_rpow_of_exponent_le hx
  convert thirdContribution_exponent hg hε hδ hδ₁ using 1
  ring

/-- Weighted smooth-divisor contribution with a negative-power saving. -/
theorem PolynomialSystem.smoothDivisorContribution_power_saving {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g) (hg : 0 < g)
    {A B ε δ x y : ℝ} {F : ArithmeticMap k} (hF : Admissible A B (ε * δ / 3) F)
    (hB : 0 ≤ B) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hx : 1 ≤ x)
    (hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x) (s : Finset ℕ) (N : ℕ+)
    {a b : ℤ} (hab : a ≤ b) (hlevel : (N : ℝ) ≤ (b : ℝ) - a)
    (hlength : (b : ℝ) - a ≤ 2 * y)
    (hinterval : ∀ t ∈ Finset.Ioc a b, (t.natAbs : ℝ) ≤ 2 * x) :
    P.smoothDivisorContribution F s N (x ^ (3 * (g : ℝ) * ε / 2)) a b ≤
      (4 * smoothDivisorBound g P.badDiscriminant s *
        (B * (((g : ℝ) + 1) * 2 ^ g) ^ (ε * δ / 3))) * y * x ^ (-(ε / 12)) * F 1 := by
  have H := P.smoothDivisorContribution_le (T := x ^ (3 * (g : ℝ) * ε / 2)) hF hB (by positivity) hx hδ
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hx) _) hheight s N hab hlevel hinterval
  rw [hdeg] at H
  let C := 2 * smoothDivisorBound g P.badDiscriminant s *
    (B * (((g : ℝ) + 1) * 2 ^ g) ^ (ε * δ / 3))
  have hC : 0 ≤ C := by dsimp [C]; positivity [smoothDivisorBound_pos g P.badDiscriminant_pos s]
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hy : 0 ≤ y := by linarith
  have H' := mul_le_mul hlength (thirdContribution_power_saving hg hε.le hδ hδ₁ hx)
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _) (by positivity)) (by positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H' hC) (hF.nonneg 1)
  apply H.trans
  dsimp only [C] at H''
  convert H'' using 1 <;> ring

end NairTenenbaum
