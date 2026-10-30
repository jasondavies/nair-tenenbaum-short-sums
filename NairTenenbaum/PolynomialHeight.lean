module

public import NairTenenbaum.PolynomialSystem

@[expose] public section

/-! # Coefficient-height bounds for polynomial values -/

namespace NairTenenbaum

open Polynomial Finset

theorem coeff_natAbs_le_height (Q : ℤ[X]) (i : ℕ) :
    (Q.coeff i).natAbs ≤ polynomialHeight Q := by
  by_cases hi : i ∈ Q.support
  · exact Finset.le_sup (f := fun i => (Q.coeff i).natAbs) hi
  · simp only [Polynomial.mem_support_iff, not_not] at hi
    simp [hi]

theorem polynomialHeight_pos {Q : ℤ[X]} (hQ : Q ≠ 0) : 0 < polynomialHeight Q :=
  (Int.natAbs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQ)).trans_le
    (coeff_natAbs_le_height Q Q.natDegree)

/-- A coefficient-uniform bound on integral polynomial values. -/
theorem eval_natAbs_le_height (Q : ℤ[X]) (n : ℤ) :
    (Q.eval n).natAbs ≤ polynomialHeight Q * (Q.natDegree + 1) *
      max 1 n.natAbs ^ Q.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ range (Q.natDegree + 1), (Q.coeff i * n ^ i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ range (Q.natDegree + 1),
        polynomialHeight Q * max 1 n.natAbs ^ Q.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Int.natAbs_mul, Int.natAbs_pow]
      apply Nat.mul_le_mul (coeff_natAbs_le_height Q i)
      exact (Nat.pow_le_pow_left (le_max_right 1 n.natAbs) i).trans
        (Nat.pow_le_pow_right (by omega : 0 < max 1 n.natAbs)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by simp; ring

theorem eval_natAbs_le_height_of_one_le (Q : ℤ[X]) {n : ℤ} (hn : 1 ≤ n.natAbs) :
    (Q.eval n).natAbs ≤ polynomialHeight Q * (Q.natDegree + 1) * n.natAbs ^ Q.natDegree := by
  simpa only [max_eq_right hn] using eval_natAbs_le_height Q n

end NairTenenbaum
