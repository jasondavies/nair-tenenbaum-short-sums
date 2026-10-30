module

public import NairTenenbaum.PolynomialSieve
public import NairTenenbaum.JointCongruence

@[expose] public section

/-! # Polynomial sieves with simultaneous congruence conditions

Conditioning on pairwise coprime polynomial congruences preserves the sifting
density at primes coprime to their moduli. The main term keeps the full joint
congruence density; the remainder costs its numerator.
-/

namespace NairTenenbaum

open Finset Nat Real Polynomial

noncomputable def polynomialCongruenceSet {r : ℕ} (R : Fin r → ℤ[X]) (m : Tuple r)
    (a b : ℤ) : Finset ℤ :=
  (Finset.Ioc a b).filter fun n => ∀ i, (m i : ℤ) ∣ (R i).eval n

noncomputable def conditionalPolynomialSieve {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) : BoundingSieve where
  support := (polynomialCongruenceSet R m a b).image (fun n => (Q.eval n).natAbs)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun d => (((polynomialCongruenceSet R m a b).filter fun n => (Q.eval n).natAbs = d).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := ((b : ℝ) - a) * ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)
  nu := rootDensity Q
  nu_mult := rootDensity_multiplicative Q
  nu_pos_of_prime := fun p hp hd => div_pos (by exact_mod_cast hroot p hp hd) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => (div_lt_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hQ p hp)

theorem conditionalPolynomialSieve_multSum {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) (d : ℕ) :
    (conditionalPolynomialSieve Q hQ P hP hroot R m a b).multSum d =
      mixedCongruenceCount Q R d m a b := by
  change (∑ e ∈ (polynomialCongruenceSet R m a b).image (fun n => (Q.eval n).natAbs),
    if d ∣ e then (((polynomialCongruenceSet R m a b).filter fun n => (Q.eval n).natAbs = e).card : ℝ) else 0) = _
  rw [sum_fiber_card_filter]
  unfold polynomialCongruenceSet mixedCongruenceCount jointCongruenceCount
  congr 2
  ext n
  simp only [Finset.mem_filter, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Int.natCast_dvd]
  tauto

theorem mixedCongruenceCount_error {r : ℕ} (Q : ℤ[X]) (R : Fin r → ℤ[X])
    {d : ℕ} (hd : 0 < d) (m : Tuple r)
    (hpair : Pairwise fun i j => Nat.Coprime (m i) (m j))
    (hcross : ∀ i, Nat.Coprime d (m i)) (a b : ℤ) (hab : a ≤ b) :
    |(mixedCongruenceCount Q R d m a b : ℝ) -
      ((rootCount Q d : ℝ) / d) * (((b : ℝ) - a) * ∏ i, ((rootCount (R i) (m i) : ℝ) / m i))| ≤
      (rootCount Q d : ℝ) * ∏ i, (rootCount (R i) (m i) : ℝ) := by
  have hpos : ∀ i : Fin (r + 1), 0 < (Fin.cons d (fun i => (m i : ℕ)) : Fin (r + 1) → ℕ) i := by
    intro i
    exact Fin.cases hd (fun i => (m i).pos) i
  have hcop : Pairwise fun i j =>
      Nat.Coprime ((Fin.cons d (fun i => (m i : ℕ)) : Fin (r + 1) → ℕ) i)
        ((Fin.cons d (fun i => (m i : ℕ)) : Fin (r + 1) → ℕ) j) := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact fun h => (h rfl).elim
    · exact fun _ => hcross j
    · exact fun _ => (hcross i).symm
    · exact fun h => hpair (fun e => h (congrArg Fin.succ e))
  have H := jointCongruenceCount_error (Fin.cons Q R) (Fin.cons d (fun i => (m i : ℕ))) hpos hcop a b hab
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_mul, Nat.cast_prod] at H
  change |(mixedCongruenceCount Q R d m a b : ℝ) - _| ≤ _ at H
  rw [Finset.prod_div_distrib]
  convert H using 2
  ring

theorem conditionalPolynomialSieve_rem_le {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r)
    (hpair : Pairwise fun i j => Nat.Coprime (m i) (m j)) (hPm : Nat.Coprime P (mass m))
    (a b : ℤ) (hab : a ≤ b) {d : ℕ} (hd : d ∣ P) :
    |(conditionalPolynomialSieve Q hQ P hP hroot R m a b).rem d| ≤
      (rootCount Q d : ℝ) * ∏ i, (rootCount (R i) (m i) : ℝ) := by
  rw [BoundingSieve.rem, conditionalPolynomialSieve_multSum]
  exact mixedCongruenceCount_error Q R (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP.ne_zero hd)) m hpair
    (fun i => (hPm.of_dvd_left hd).of_dvd_right (coordinate_dvd_mass m i)) a b hab

noncomputable def conditionalPolynomialSiftedCount {r : ℕ} (Q : ℤ[X]) (P : ℕ)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) : ℕ :=
  ((polynomialCongruenceSet R m a b).filter fun n => Nat.Coprime P (Q.eval n).natAbs).card

theorem conditionalPolynomialSieve_siftedSum {r : ℕ} (Q : ℤ[X]) (hQ : NoFixedPrimeDivisor Q)
    (P : ℕ) (hP : Squarefree P) (hroot : ∀ p, p.Prime → p ∣ P → 0 < rootCount Q p)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) :
    (conditionalPolynomialSieve Q hQ P hP hroot R m a b).siftedSum =
      conditionalPolynomialSiftedCount Q P R m a b :=
  sum_fiber_card_filter (polynomialCongruenceSet R m a b) (fun n => (Q.eval n).natAbs) (Nat.Coprime P)

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
  obtain ⟨K, hK, H⟩ := exists_selberg_upper_bound hg hη
  refine ⟨K, hK, ?_⟩
  intro Q hQ hdeg P hP hroot r R m hpair hPm a b z hab hz hzlog hprimes
  let s := conditionalPolynomialSieve Q hQ P hP hroot R m a b
  let C : ℝ := ∏ i, (rootCount (R i) (m i) : ℝ)
  have hC : 0 ≤ C := Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hdim (p : ℕ) (hp : p ∈ s.prodPrimes.primeFactors) : s.nu p ≤ g / p := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
    have Hr : (rootCount Q p : ℝ) ≤ Q.natDegree := by exact_mod_cast rootCount_le_degree hQ (Nat.prime_of_mem_primeFactors hp)
    exact Hr.trans hdeg
  have hgap (p : ℕ) (hp : p ∈ s.prodPrimes.primeFactors) : s.nu p ≤ 1 - 1 / (p : ℝ) := by
    have hp₀ : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have Hr : (rootCount Q p : ℝ) + 1 ≤ p := by exact_mod_cast hQ p (Nat.prime_of_mem_primeFactors hp)
    change (rootCount Q p : ℝ) / p ≤ _
    apply (div_le_iff₀ hp₀).mpr
    field_simp
    linarith
  have herr (d : ℕ) (hd : d ∣ s.prodPrimes) : |s.rem d| ≤ C * g ^ d.primeFactors.card := by
    calc
      _ ≤ (rootCount Q d : ℝ) * C := conditionalPolynomialSieve_rem_le Q hQ P hP hroot R m hpair hPm a b hab hd
      _ ≤ g ^ d.primeFactors.card * C := mul_le_mul_of_nonneg_right
        (rootCount_squarefree_le hQ hdeg (hP.squarefree_of_dvd hd)) hC
      _ = _ := mul_comm _ _
  have hmass : 0 ≤ s.totalMass := mul_nonneg (by exact_mod_cast sub_nonneg.mpr hab)
    (Finset.prod_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have HB := H s z C hz hzlog hC hmass hprimes hdim hgap herr
  dsimp only [s] at HB
  rw [conditionalPolynomialSieve_siftedSum] at HB
  simpa only [conditionalPolynomialSieve, rootDensity_apply, C, mul_assoc, mul_comm, mul_left_comm] using HB

end NairTenenbaum
