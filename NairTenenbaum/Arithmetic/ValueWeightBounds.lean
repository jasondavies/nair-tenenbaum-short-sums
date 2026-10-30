/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import NairTenenbaum.Polynomials.PolynomialValueBounds
public import NairTenenbaum.Polynomials.PolynomialValueTuples

/-! # Pointwise arithmetic-weight bounds under the height hypothesis -/

@[expose] public section

namespace NairTenenbaum

theorem Admissible.extend_le_mass_rpow {k : ℕ} {A B σ : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B σ F) (hB : 0 ≤ B) (n : Fin k → ℕ) :
    extendArithmeticMap F n ≤ B * ((∏ j, n j : ℕ) : ℝ) ^ σ * F 1 := by
  unfold extendArithmeticMap
  split_ifs with hn
  · have H := (hF.le_at_one (fun j => ⟨n j, hn j⟩)).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (hF.nonneg 1))
    exact H
  · exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hF.nonneg 1)

/-- The polynomial-height constant is kept outside the power of `x`, which
preserves the exponent saving in the second contribution. -/
theorem PolynomialSystem.value_weight_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    (hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x) {t : ℤ} (ht : (t.natAbs : ℝ) ≤ 2 * x) :
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs) ≤
      B * (((P.total.natDegree : ℝ) + 1) * 2 ^ P.total.natDegree) ^ σ *
        x ^ (((P.total.natDegree : ℝ) + 1 / δ) * σ) * F 1 := by
  have heq : (∏ j, ((P.Q j).eval t).natAbs) = (P.total.eval t).natAbs := by
    simp only [PolynomialSystem.total, Polynomial.eval_prod]
    exact (map_prod Int.natAbsHom _ _).symm
  have H := hF.extend_le_mass_rpow hB (fun j => ((P.Q j).eval t).natAbs)
  rw [heq] at H
  apply H.trans
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (eval_natAbs_le_const_rpow_of_height rfl hx hδ hheight ht) hσ
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (zero_le_one.trans hx) _),
    ← Real.rpow_mul (zero_le_one.trans hx)] at hpow
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hB) (hF.nonneg 1)

end NairTenenbaum
