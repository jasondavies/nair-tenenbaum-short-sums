module

public import NairTenenbaum.IdealMultiplicityVectors

@[expose] public section

/-! # Residue-degree totals and prime-norm ideal counts -/

namespace NairTenenbaum

open Finset NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

theorem primeIdealSupport_weighted_degree_eq {p : ℕ} (hp : p.Prime) :
    (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ *
      (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count P.1) = Module.finrank ℚ K := by
  apply Nat.pow_right_injective hp.two_le
  change p ^ (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ *
    (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count P.1) = p ^ Module.finrank ℚ K
  rw [← idealOfMultiplicities_norm hp (fun P =>
      (normalizedFactors (Ideal.span {(p : 𝓞 K)})).count P.1),
    idealOfMultiplicities_factor_counts (span_prime_natCast_ne_bot hp) (primeIdealSupport K p)
      (show (normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset ⊆ primeIdealSupport K p from Subset.refl _),
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem primeIdealSupport_sum_inertiaDeg_le {p : ℕ} (hp : p.Prime) :
    (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ) ≤ Module.finrank ℚ K := by
  rw [← primeIdealSupport_weighted_degree_eq hp]
  apply sum_le_sum
  intro P _
  apply Nat.le_mul_of_pos_right
  exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.2)

noncomputable def primeNormIdealResidueDegreeOneEquiv {p : ℕ} (hp : p.Prime) :
    {I : Ideal (𝓞 K) // absNorm I = p} ≃
      {P : primeIdealSupport K p // P.1.inertiaDeg ℤ = 1} where
  toFun I := by
    have hP : Prime I.1 := UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (Ideal.irreducible_of_irreducible_absNorm (by rw [I.2]; exact (Nat.prime_iff.mp hp).irreducible))
    have hbelow := rationalPrimeBelow_eq_of_dvd_primePowerNorm hP hp
      (show absNorm I.1 = p ^ 1 by simpa using I.2) dvd_rfl
    have hmem := (primeIdealSupport_mem_iff hp).mpr ⟨hP, hbelow⟩
    refine ⟨⟨I.1, hmem⟩, ?_⟩
    apply Nat.pow_right_injective hp.two_le
    change p ^ I.1.inertiaDeg ℤ = p ^ 1
    rw [← primeIdealSupport_norm hp hmem, pow_one, I.2]
  invFun P := ⟨P.1.1, by rw [primeIdealSupport_norm hp P.1.2, P.2, pow_one]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem idealNormCount_prime_eq_card_residueDegreeOne {p : ℕ} (hp : p.Prime) :
    idealNormCount K p = Nat.card {P : primeIdealSupport K p // P.1.inertiaDeg ℤ = 1} :=
  Nat.card_congr (primeNormIdealResidueDegreeOneEquiv hp)

theorem idealNormCount_prime_eq_sum_residueDegreeOne {p : ℕ} (hp : p.Prime) :
    (idealNormCount K p : ℝ) =
      ∑ P : primeIdealSupport K p, if P.1.inertiaDeg ℤ = 1 then (P.1.inertiaDeg ℤ : ℝ) else 0 := by
  classical
  rw [idealNormCount_prime_eq_card_residueDegreeOne hp]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro P _
  split_ifs with h
  · simp [h]
  · simp

end NairTenenbaum
