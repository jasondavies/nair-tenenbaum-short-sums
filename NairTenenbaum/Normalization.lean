module

public import NairTenenbaum.PolynomialSystem

@[expose] public section

/-! # Normalization at the unit tuple

The reductions at the start of Lemma 2 and of the completion of Theorem 1 (§4).
These are reductions only: no analytic bound is assumed or exported as a theorem
without the corresponding explicit hypothesis.
-/

namespace NairTenenbaum

open Finset

noncomputable def normalize {k : ℕ} (F : ArithmeticMap k) : ArithmeticMap k :=
  fun n => F n / F 1

theorem Admissible.normalize {k : ℕ} {A B ε : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) : Admissible A B ε (normalize F) := by
  have heq : NairTenenbaum.normalize F = fun n => (F 1)⁻¹ * F n := by
    funext n
    exact div_eq_inv_mul _ _
  rw [heq]
  exact hF.smul (inv_nonneg.mpr (hF.nonneg 1))

theorem normalize_one {k : ℕ} {F : ArithmeticMap k} (hF : F 1 ≠ 0) : normalize F 1 = 1 :=
  div_self hF

theorem scale_normalize {k : ℕ} {F : ArithmeticMap k} (hF : F 1 ≠ 0) :
    (fun n => F 1 * normalize F n) = F := by
  funext n
  exact mul_div_cancel₀ (F n) hF

theorem weight_smul {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ)
    (F : ArithmeticMap k) (θ : Fin r → ℕ → ℝ) (N : ℕ+) (c : ℝ) :
    weight γ D (fun n => c * F n) θ N = c * weight γ D F θ N := by
  simp only [weight, pullback, ← mul_assoc, Finset.mul_sum]

theorem extendArithmeticMap_smul {k : ℕ} (F : ArithmeticMap k) (n : Fin k → ℕ) (c : ℝ) :
    extendArithmeticMap (fun m => c * F m) n = c * extendArithmeticMap F n := by
  unfold extendArithmeticMap
  split_ifs <;> simp

theorem shortSum_smul {k : ℕ} (Q : Fin k → Polynomial ℤ) (F : ArithmeticMap k)
    (x y c : ℝ) : shortSum Q (fun n => c * F n) x y = c * shortSum Q F x y := by
  simp only [shortSum, extendArithmeticMap_smul, Finset.mul_sum]

theorem mainTerm_smul {k r : ℕ} (P : PolynomialSystem k r) (F : ArithmeticMap k)
    (x y c : ℝ) : mainTerm P (fun n => c * F n) x y = c * mainTerm P F x y := by
  simp only [mainTerm, PolynomialSystem.weight, weight_smul, ← Finset.mul_sum]
  ring

@[simp] theorem shortSum_zero {k : ℕ} (Q : Fin k → Polynomial ℤ) (x y : ℝ) :
    shortSum Q 0 x y = 0 := by
  have h := shortSum_smul Q (0 : ArithmeticMap k) x y 0
  simp only [zero_mul] at h
  exact h

@[simp] theorem mainTerm_zero {k r : ℕ} (P : PolynomialSystem k r) (x y : ℝ) :
    mainTerm P 0 x y = 0 := by
  have h := mainTerm_smul P (0 : ArithmeticMap k) x y 0
  simp only [zero_mul] at h
  exact h

/-- It suffices to prove a homogeneous short-sum bound for functions with `F(1)=1`.
The constant `C` is fixed before the function is chosen. -/
theorem bound_of_normalized_bound {k r : ℕ} {A B ε C x y : ℝ}
    (P : PolynomialSystem k r)
    (h : ∀ H : ArithmeticMap k, Admissible A B ε H → H 1 = 1 →
      shortSum P.Q H x y ≤ C * mainTerm P H x y)
    {F : ArithmeticMap k} (hF : Admissible A B ε F) :
    shortSum P.Q F x y ≤ C * mainTerm P F x y := by
  by_cases hzero : F 1 = 0
  · rw [hF.eq_zero_of_one hzero, shortSum_zero, mainTerm_zero, mul_zero]
  · have hnorm := h (normalize F) hF.normalize (normalize_one hzero)
    have hscaled := mul_le_mul_of_nonneg_left hnorm (hF.nonneg 1)
    have hl := shortSum_smul P.Q (normalize F) x y (F 1)
    have hr := mainTerm_smul P (normalize F) x y (F 1)
    rw [scale_normalize hzero] at hl hr
    rw [hl, hr]
    nlinarith [hscaled]

end NairTenenbaum
