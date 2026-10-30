/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import NairTenenbaum.Sieve.LocalConditionalSieve

/-! # Polynomial sieves with simultaneous congruence conditions

Conditioning on pairwise coprime polynomial congruences preserves the sifting
density at primes coprime to their moduli. The main term keeps the full joint
congruence density; the remainder costs its numerator.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

/-- The global no-fixed-prime specialization of the local conditional sieve. -/
noncomputable def conditionalPolynomialSieve {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) : BoundingSieve :=
  localConditionalPolynomialSieve Q P hP (fun p hp _ => hQ p hp) hroot R m a b

theorem conditionalPolynomialSieve_multSum {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) (d : ℕ) :
    (conditionalPolynomialSieve Q hQ P hP hroot R m a b).multSum d =
      mixedCongruenceCount Q R d m a b :=
  localConditionalPolynomialSieve_multSum Q P hP (fun p hp _ => hQ p hp) hroot R m a b d

theorem conditionalPolynomialSieve_rem_le {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r)
    (hpair : Pairwise fun i j => Nat.Coprime (m i) (m j)) (hPm : Nat.Coprime P (mass m))
    (a b : ℤ) (hab : a ≤ b) {d : ℕ} (hd : d ∣ P) :
    |(conditionalPolynomialSieve Q hQ P hP hroot R m a b).rem d| ≤
      (rootCount Q d : ℝ) * ∏ i, (rootCount (R i) (m i) : ℝ) :=
  localConditionalPolynomialSieve_rem_le Q P hP (fun p hp _ => hQ p hp) hroot
    R m hpair hPm a b hab hd

theorem conditionalPolynomialSieve_siftedSum {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) :
    (conditionalPolynomialSieve Q hQ P hP hroot R m a b).siftedSum =
      conditionalPolynomialSiftedCount Q P R m a b :=
  localConditionalPolynomialSieve_siftedSum Q P hP (fun p hp _ => hQ p hp) hroot R m a b

/-- The congruence density remains in the main term; its numerator controls
the error. The constant is uniform in the congruence polynomials and moduli. -/
theorem exists_conditional_polynomial_sieve_bound {g η : ℝ} (hg : 1 ≤ g) (hη : 0 < η) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → (Q.natDegree : ℝ) ≤ g →
      ∀ (P : ℕ), Squarefree P → (∀ p, p.Prime → p ∣ P → 0 < rootCount Q p) →
      ∀ (r : ℕ) (R : Fin r → ℤ[X]) (m : Tuple r),
      (Pairwise fun i j => Nat.Coprime (m i) (m j)) → Nat.Coprime P (mass m) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      (∀ p ∈ P.primeFactors, (p : ℝ) ≤ z) →
      (conditionalPolynomialSiftedCount Q P R m a b : ℝ) ≤
        4 * ((b : ℝ) - a) * (∏ i, ((rootCount (R i) (m i) : ℝ) / m i)) *
          (∏ p ∈ P.primeFactors, (1 - (rootCount Q p : ℝ) / p)) +
        K * (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ (4 * g * (1 + η)) := by
  obtain ⟨K, hK, H⟩ := exists_local_conditional_polynomial_sieve_bound hg hη
  refine ⟨K, hK, ?_⟩
  intro Q hQ hdeg P hP hroot
  apply H Q P hP (fun p hp _ => hQ p hp) _ hroot
  intro p hp _
  exact (Nat.cast_le.mpr (rootCount_le_degree hQ hp)).trans hdeg

end NairTenenbaum
