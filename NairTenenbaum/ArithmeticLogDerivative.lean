module

public import NairTenenbaum.IdealLocalEulerPolynomial
public import NairTenenbaum.ConvolutionMean

@[expose] public section

/-! # Logarithmic weighting and Dirichlet convolution

Logarithmic weighting is a derivation for Dirichlet convolution. The ideal
von Mangoldt function is the logarithmically weighted ideal count convolved
with its proved Dirichlet inverse.
-/

namespace NairTenenbaum

open Finset ArithmeticFunction NumberField

noncomputable def arithmeticLogWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f.pmul ArithmeticFunction.log

@[simp] theorem arithmeticLogWeight_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticLogWeight f n = f n * Real.log n := rfl

theorem arithmeticLogWeight_mul (f g : ArithmeticFunction ℝ) :
    arithmeticLogWeight (f * g) = arithmeticLogWeight f * g + f * arithmeticLogWeight g := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  simp only [arithmeticLogWeight_apply, ArithmeticFunction.add_apply, mul_apply, sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro de hde
  obtain ⟨heq, _⟩ := Nat.mem_divisorsAntidiagonal.mp hde
  have hd : de.1 ≠ 0 := by intro h; simp [h] at heq; exact hn heq.symm
  have he : de.2 ≠ 0 := by intro h; simp [h] at heq; exact hn heq.symm
  rw [← heq, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hd) (Nat.cast_ne_zero.mpr he)]
  ring

@[simp] theorem arithmeticLogWeight_one : arithmeticLogWeight 1 = 0 := by
  ext n
  by_cases hn : n = 1
  · simp [hn]
  · simp [arithmeticLogWeight_apply, one_apply_ne hn]

noncomputable def arithmeticLogDerivative (f g : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  arithmeticLogWeight f * g

theorem arithmeticLogDerivative_convolution {f g : ArithmeticFunction ℝ} (hfg : f * g = 1) :
    f * arithmeticLogDerivative f g = arithmeticLogWeight f := by
  unfold arithmeticLogDerivative
  calc
    _ = arithmeticLogWeight f * (f * g) := by ring
    _ = _ := by rw [hfg, mul_one]

variable (K : Type*) [Field K] [NumberField K]

noncomputable def idealVonMangoldt : ArithmeticFunction ℝ :=
  arithmeticLogDerivative (idealNormArithmetic K) (idealNormInverse K)

theorem idealVonMangoldt_convolution :
    idealNormArithmetic K * idealVonMangoldt K = arithmeticLogWeight (idealNormArithmetic K) :=
  arithmeticLogDerivative_convolution (idealNormArithmetic_mul_inverse K)

theorem idealVonMangoldt_summatory_identity (x : ℝ) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, (idealNormCount K n : ℝ) * Real.log n) =
      ∑' d : ℕ, idealVonMangoldt K d * arithmeticSummatory (idealNormArithmetic K) (x / d) := by
  rw [← arithmeticSummatory_mul, mul_comm, idealVonMangoldt_convolution]
  unfold arithmeticSummatory
  apply sum_congr rfl
  intro n hn
  rw [arithmeticLogWeight_apply, idealNormArithmetic_apply_pos K (mem_Icc.mp hn).1]

theorem idealVonMangoldt_one : idealVonMangoldt K 1 = 0 := by
  simp [idealVonMangoldt, arithmeticLogDerivative]

theorem idealVonMangoldt_prime {p : ℕ} (hp : p.Prime) :
    idealVonMangoldt K p = (idealNormCount K p : ℝ) * Real.log p := by
  unfold idealVonMangoldt arithmeticLogDerivative
  rw [arithmeticFunction_mul_prime _ _ hp, arithmeticLogWeight_apply,
    arithmeticLogWeight_apply, Nat.cast_one, Real.log_one, mul_zero, zero_mul, zero_add,
    (idealNormInverse_isMultiplicative K).1, mul_one, idealNormArithmetic_apply_pos K hp.pos]

end NairTenenbaum
