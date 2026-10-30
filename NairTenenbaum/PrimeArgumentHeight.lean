module

public import NairTenenbaum.PolynomialValueBounds

@[expose] public section

/-! # The height and growth margins for Theorem 3

Only one eighth of a power is spent absorbing the degree-dependent evaluation
constant. This leaves a positive saving at the paper's exponent `εδ/3`.
-/

namespace NairTenenbaum

open Polynomial

theorem primeArgument_growth_margin {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ((g : ℝ) + 1 / δ + 1 / 8) * (ε * δ / 3) ≤ 17 * (g : ℝ) * ε / 24 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hgd := mul_le_mul_of_nonneg_left hδ₁ (Nat.cast_nonneg g : (0 : ℝ) ≤ g)
  have hinner : (g : ℝ) * δ + 1 + δ / 8 ≤ 17 * (g : ℝ) / 8 := by nlinarith
  calc
    _ = ε * ((g : ℝ) * δ + 1 + δ / 8) / 3 := by field_simp
    _ ≤ ε * (17 * (g : ℝ) / 8) / 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hε) (by norm_num)
    _ = _ := by ring

theorem eval_natAbs_le_primeArgument_rpow {Q : ℤ[X]} {g : ℕ} (hdeg : Q.natDegree = g)
    {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ)
    (hheight : (polynomialHeight Q : ℝ) ^ δ ≤ x)
    (hlarge : (((g : ℝ) + 1) * 2 ^ g) ^ (8 : ℕ) ≤ x)
    {t : ℤ} (ht : (t.natAbs : ℝ) ≤ 2 * x) :
    ((Q.eval t).natAbs : ℝ) ≤ x ^ ((g : ℝ) + 1 / δ + 1 / 8) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hconst : ((g : ℝ) + 1) * 2 ^ g ≤ x ^ (1 / 8 : ℝ) := by
    have H := Real.rpow_le_rpow (by positivity) hlarge (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at H
    norm_num at H
    exact H
  calc
    _ ≤ (((g : ℝ) + 1) * 2 ^ g) * x ^ ((g : ℝ) + 1 / δ) :=
      eval_natAbs_le_const_rpow_of_height hdeg hx hδ hheight ht
    _ ≤ x ^ (1 / 8 : ℝ) * x ^ ((g : ℝ) + 1 / δ) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

end NairTenenbaum
