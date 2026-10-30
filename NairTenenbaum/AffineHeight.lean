module

public import NairTenenbaum.AffinePolynomialSystem
public import NairTenenbaum.PolynomialHeight

@[expose] public section

/-! # Coefficient height after arithmetic-progression substitution

The degree-only factor is retained explicitly: a translate can increase the
height even when the progression modulus is one.
-/

namespace NairTenenbaum

open Polynomial Finset

/-- Every coefficient of an affine power is bounded by the corresponding
power of the sum of the absolute coefficients. -/
theorem coeff_affine_pow_natAbs_le (q : ℕ) (a : ℤ) (i j : ℕ) :
    ((affinePolynomial q a ^ i).coeff j).natAbs ≤ (q + a.natAbs) ^ i := by
  induction i generalizing j with
  | zero =>
    simp only [pow_zero, Polynomial.coeff_one]
    split_ifs <;> norm_num
  | succ i ih =>
    cases j with
    | zero =>
      have heq : ((affinePolynomial q a) ^ (i + 1)).coeff 0 =
          ((affinePolynomial q a) ^ i).coeff 0 * a := by
        rw [pow_succ]
        simp only [affinePolynomial, mul_add, ← mul_assoc, Polynomial.coeff_add,
          Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C, zero_add]
      rw [heq, Int.natAbs_mul, pow_succ]
      exact Nat.mul_le_mul (ih 0) (Nat.le_add_left _ _)
    | succ j =>
      have heq : ((affinePolynomial q a) ^ (i + 1)).coeff (j + 1) =
          ((affinePolynomial q a) ^ i).coeff j * (q : ℤ) +
            ((affinePolynomial q a) ^ i).coeff (j + 1) * a := by
        rw [pow_succ]
        simp only [affinePolynomial, mul_add, ← mul_assoc, Polynomial.coeff_add,
          Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
      rw [heq]
      calc
        _ ≤ _ := Int.natAbs_add_le _ _
        _ = ((affinePolynomial q a ^ i).coeff j).natAbs * q +
            ((affinePolynomial q a ^ i).coeff (j + 1)).natAbs * a.natAbs := by
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
        _ ≤ (q + a.natAbs) ^ i * q + (q + a.natAbs) ^ i * a.natAbs :=
          Nat.add_le_add (Nat.mul_le_mul_right q (ih j)) (Nat.mul_le_mul_right a.natAbs (ih (j + 1)))
        _ = _ := by rw [← Nat.mul_add, pow_succ]

/-- Coefficientwise height bound for affine composition. -/
theorem coeff_comp_affine_natAbs_le (Q : ℤ[X]) (q : ℕ) (a : ℤ) (j : ℕ) (hq : 0 < q) :
    ((Q.comp (affinePolynomial q a)).coeff j).natAbs ≤
      (Q.natDegree + 1) * polynomialHeight Q * (q + a.natAbs) ^ Q.natDegree := by
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range, Polynomial.finsetSum_coeff]
  calc
    _ ≤ ∑ i ∈ range (Q.natDegree + 1),
        ((C (Q.coeff i) * affinePolynomial q a ^ i).coeff j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ range (Q.natDegree + 1), polynomialHeight Q * (q + a.natAbs) ^ Q.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Polynomial.coeff_C_mul, Int.natAbs_mul]
      apply Nat.mul_le_mul (coeff_natAbs_le_height Q i)
      exact (coeff_affine_pow_natAbs_le q a i j).trans
        (Nat.pow_le_pow_right (by omega : 0 < q + a.natAbs) (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by simp; ring

/-- A uniform bound sufficient for the height threshold in Corollary 1. -/
theorem polynomialHeight_comp_affine_le (Q : ℤ[X]) (q : ℕ) (a : ℤ) (hq : 0 < q)
    (ha : a.natAbs ≤ q) :
    polynomialHeight (Q.comp (affinePolynomial q a)) ≤
      (Q.natDegree + 1) * polynomialHeight Q * (2 * q) ^ Q.natDegree := by
  apply Finset.sup_le
  intro j _
  apply (coeff_comp_affine_natAbs_le Q q a j hq).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : q + a.natAbs ≤ 2 * q) _)

end NairTenenbaum
