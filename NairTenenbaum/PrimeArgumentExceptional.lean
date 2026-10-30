module

public import NairTenenbaum.ValueBoundContributions

@[expose] public section

/-! # Power savings with the growth margin of Theorem 3

The admissibility exponent `εδ/3` leaves a smaller positive gap than the
progression bound requires. Keeping that gap explicit avoids strengthening
the hypotheses on the arithmetic function.
-/

namespace NairTenenbaum

theorem PolynomialSystem.primePowerContribution_primeArgument_power_saving {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g)
    {A B σ ε c x y : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hx : 1 ≤ x)
    (hmargin : c * σ ≤ 17 * (g : ℝ) * ε / 24) {a b : ℤ} (hab : a ≤ b)
    (hlevel : (x ^ ((g : ℝ) * ε / 2)) ^ 4 ≤ (b : ℝ) - a)
    (hlen : (b : ℝ) - a ≤ 2 * y)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.primePowerContribution F (x ^ ((g : ℝ) * ε / 2)) a b ≤
      (8 * (g : ℝ) * (max g (P.badDiscriminant ^ 3) : ℕ) * B) *
        y * x ^ (-((g : ℝ) * ε / 24)) * F 1 := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hz : 1 ≤ x ^ ((g : ℝ) * ε / 2) := Real.one_le_rpow hx (by positivity)
  have H := P.primePowerContribution_le_of_value_bound hF hB hσ hx₀.le hz hab hlevel hvalue
  rw [hdeg] at H
  have Hpow : x ^ (c * σ) / (x ^ ((g : ℝ) * ε / 2)) ^ 2 ≤ x ^ (-((g : ℝ) * ε / 24)) := by
    have heq : (x ^ ((g : ℝ) * ε / 2)) ^ 2 = x ^ ((g : ℝ) * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx₀.le]
      congr 1
      norm_num
    rw [heq, ← Real.rpow_sub hx₀]
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith [mul_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ _) hε]
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hy : 0 ≤ y := by linarith
  have H' := mul_le_mul hlen Hpow (by positivity) (by positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H'
    (by positivity : 0 ≤ 4 * (g : ℝ) * (max g (P.badDiscriminant ^ 3) : ℕ) * B)) (hF.nonneg 1)
  apply H.trans
  convert H'' using 1 <;> ring

/-- The same growth margin pays the smooth-divisor saving. -/
theorem PolynomialSystem.smoothDivisorContribution_primeArgument_power_saving {k r g : ℕ}
    (P : PolynomialSystem k r) (hdeg : P.total.natDegree = g)
    {A B σ ε c x y : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hx : 1 ≤ x)
    (hmargin : c * σ ≤ 17 * (g : ℝ) * ε / 24) (s : Finset ℕ) (N : ℕ+)
    {a b : ℤ} (hab : a ≤ b) (hlevel : (N : ℝ) ≤ (b : ℝ) - a)
    (hlen : (b : ℝ) - a ≤ 2 * y)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.smoothDivisorContribution F s N (x ^ (3 * (g : ℝ) * ε / 2)) a b ≤
      (4 * smoothDivisorBound g P.badDiscriminant s * B) *
        y * x ^ (-((g : ℝ) * ε / 24)) * F 1 := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have H := P.smoothDivisorContribution_le_of_value_bound (T := x ^ (3 * (g : ℝ) * ε / 2)) hF hB hσ hx₀.le
    (Real.rpow_pos_of_pos hx₀ _) s N hab hlevel hvalue
  rw [hdeg] at H
  have Hpow : x ^ (c * σ) * (x ^ (3 * (g : ℝ) * ε / 2)) ^ (-(1 / 2 : ℝ)) ≤
      x ^ (-((g : ℝ) * ε / 24)) := by
    rw [← Real.rpow_mul hx₀.le, ← Real.rpow_add hx₀]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hy : 0 ≤ y := by linarith
  have H' := mul_le_mul hlen Hpow (by positivity) (by positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H'
    (by positivity [smoothDivisorBound_pos g P.badDiscriminant_pos s] :
      0 ≤ 2 * smoothDivisorBound g P.badDiscriminant s * B)) (hF.nonneg 1)
  apply H.trans
  convert H'' using 1 <;> ring

end NairTenenbaum
