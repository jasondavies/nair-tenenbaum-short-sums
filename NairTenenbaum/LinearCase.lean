module

public import NairTenenbaum.PolynomialSystem

@[expose] public section

/-! # The linear specialization

An explicit instance of the polynomial hypotheses and the simplification of the
weight and main term when `Q(X)=X`. This checks that the statement surface admits
the paper's basic example and that the dagger restriction simplifies correctly.
-/

namespace NairTenenbaum

open Polynomial Finset

noncomputable def linearSystem : PolynomialSystem 1 1 where
  Q := fun _ => X
  R := fun _ => X
  exponent := identityExponents 1
  sign := fun _ => 1
  sign_abs := by simp
  factorization := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [identityExponents]
  irreducible := by intro h; simpa using (Polynomial.irreducible_X (R := ℚ))
  nonassociated := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  exponent_pos := by intro h; simp
  noFixedPrime := by simpa using noFixedPrimeDivisor_X

@[simp] theorem linearSystem_total : linearSystem.total = (X : ℤ[X]) := by
  simp [PolynomialSystem.total, linearSystem]

@[simp] theorem linearSystem_radical : linearSystem.radical = (X : ℤ[X]) := by
  simp [PolynomialSystem.radical, linearSystem]

@[simp] theorem linearSystem_discriminant : linearSystem.discriminant = 1 := by
  rw [PolynomialSystem.discriminant, linearSystem_radical,
    Polynomial.discr_of_degree_eq_one (by simp)]
  rfl

@[simp] theorem linearSystem_badDiscriminant : linearSystem.badDiscriminant = 1 := by
  simp [PolynomialSystem.badDiscriminant]

@[simp] theorem linearSystem_weight (F : ArithmeticMap 1) (N : ℕ+) :
    linearSystem.weight F N = F (fun _ => N) / (N : ℝ) := by
  unfold PolynomialSystem.weight
  rw [linearSystem_discriminant]
  change weight (identityExponents 1) 1 F (fun _ n => (rootCount (X : ℤ[X]) n : ℝ)) N = _
  rw [weight_one_variable]
  simp

theorem linearSystem_mainTerm (F : ArithmeticMap 1) (x y : ℝ) :
    mainTerm linearSystem F x y =
      y * sieveProduct (X : ℤ[X]) x * ∑ n ∈ positiveUpTo x, F (fun _ => n) / (n : ℝ) := by
  simp [mainTerm]

theorem polynomialSystem_nonempty : Nonempty (PolynomialSystem 1 1) := ⟨linearSystem⟩

end NairTenenbaum
