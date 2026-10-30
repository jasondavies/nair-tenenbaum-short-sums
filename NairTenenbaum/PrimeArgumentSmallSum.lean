module

public import NairTenenbaum.PrimeArgumentSmallSieve
public import NairTenenbaum.PrimeArgumentMajorant

@[expose] public section

/-! # The prime-argument sieve in the original divisor tuple variables -/

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem primeArgumentSieveModulus_badSieveModuli {r : ℕ} (Q : ℤ[X]) (g : ℕ)
    (u v : Tuple r) (z : ℝ) :
    primeArgumentSieveModulus Q g (mass (badSieveModuli u v)) z =
      primeArgumentSieveModulus Q g (mass (u * v)) z := by
  unfold primeArgumentSieveModulus sieveModulus
  congr 1
  ext p
  by_cases hp : p.Prime
  · simp only [sievePrimeSet, Finset.mem_filter, Finset.mem_range, hp, and_true,
      mass_badSieveModuli, mass_mul, hp.dvd_mul, prime_dvd_mass_iff_tupleLCM u hp]
  · simp [sievePrimeSet, hp]

theorem PolynomialSystem.primeSmallDivisorSiftedSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (g : ℕ) (N : ℕ+) (a b : ℤ) (z : ℝ) :
    P.primeSmallDivisorSiftedSum F g N a b z ≤
      ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        ∑ u ∈ smallBadParts P.exponent P.badDiscriminant v N,
          pullback P.exponent F (u * v) * P.primeArgumentBadSiftedCount g u v a b z := by
  classical
  let count := fun m => conditionalPolynomialSiftedCount (P.total * X) (primeArgumentSieveModulus P.total g (mass m) z) P.R m a b
  let T := (smallDivisorTuples P.exponent N).filter (fun m => count m ≠ 0)
  let f : Tuple r → ℝ := fun m => pullback P.exponent F m * count m
  let e : Tuple r → (Σ _v : Tuple r, Tuple r) := fun m =>
    ⟨primeReject m P.discriminant.primeFactors, primeSelect m P.discriminant.primeFactors⟩
  let V := (weightUpTo P.exponent P.discriminant N).sigma (fun v => smallBadParts P.exponent P.badDiscriminant v N)
  let w : (Σ _v : Tuple r, Tuple r) → ℝ := fun t =>
    pullback P.exponent F (t.2 * t.1) * P.primeArgumentBadSiftedCount g t.2 t.1 a b z
  have heprod (m : Tuple r) : (e m).2 * (e m).1 = m := primeSelect_mul_primeReject _ _
  have heinj : Function.Injective e := by
    intro m n h
    simpa only [heprod] using congrArg (fun t : Σ _v : Tuple r, Tuple r => t.2 * t.1) h
  have himage : Finset.image e T ⊆ V := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
    have hmass := (Finset.mem_filter.mp hm).2
    have hcpos : 0 < count m := Nat.pos_of_ne_zero hc
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hcpos
    have hdiv : ∀ i, (m i : ℕ) ∣ ((P.R i).eval n).natAbs := by
      have H := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      intro i
      exact Int.natCast_dvd.mp (H i)
    apply Finset.mem_sigma.mpr
    constructor
    · apply (mem_weightUpTo P.exponent P.exponent_pos P.discriminant N _).mpr
      refine ⟨?_, P.divisor_primeReject_dagger n m hdiv⟩
      have H := Nat.le_mul_of_pos_left (weightedMass P.exponent (e m).1)
        (weightedMass_pos P.exponent (e m).2)
      rw [← weightedMass_mul, heprod] at H
      exact H.trans hmass
    · apply (mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant _ _ N).mpr
      refine ⟨P.divisor_primeSelect_bad_support n m hdiv, ?_⟩
      simpa only [heprod] using hmass
  have hew (m : Tuple r) : f m = w (e m) := by
    dsimp only [f, w, count]
    rw [heprod]
    unfold PolynomialSystem.primeArgumentBadSiftedCount
    rw [primeArgumentSieveModulus_badSieveModuli, heprod]
  have hrestrict : P.primeSmallDivisorSiftedSum F g N a b z = ∑ m ∈ T, f m := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hnot
    have hc : count m = 0 := by by_contra h; exact hnot (Finset.mem_filter.mpr ⟨hm, h⟩)
    simp only [f, hc, Nat.cast_zero, mul_zero]
  rw [hrestrict]
  have H := Finset.sum_le_sum_of_injOn e heinj.injOn himage (fun m _ => (hew m).le)
    (fun t _ _ => mul_nonneg (hF _) (Nat.cast_nonneg _))
  simpa only [V, w, Finset.sum_sigma] using H

/-- The corrected small-divisor sieve estimate in the original, unsplit tuple
variables. A single level condition on `N` controls every tuple in the sum. -/
theorem exists_primeSmallDivisorSiftedSum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g → P.total.eval 0 ≠ 0 →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (N : ℕ+) (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      L * (N : ℝ) * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a →
      P.primeSmallDivisorSiftedSum F g N a b z ≤
        K * primeArgumentSmallSieveCost B ε g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct P.total z *
          (∑ n ∈ Finset.Icc 1 N, P.weight F n) * primeArgumentFactor P.total z := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeArgument_small_sieve_sum_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg hzero A B ε F hF hA hB hε hsmall N a b z hab hz hzlog hlevel
  refine (P.primeSmallDivisorSiftedSum_le_split hF.nonneg g N a b z).trans ?_
  apply H k r P hdeg hzero A B ε F hF hA hB hε hsmall N
    (fun v => smallBadParts P.exponent P.badDiscriminant v N)
    (fun v _ u hu => ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).1)
    a b z hab hz hzlog
  intro v _ u hu
  have huN := ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).2
  have hmod := (mass_badSieveModuli_le_weightedMass P.exponent P.exponent_pos u v).trans huN
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmod : (mass (badSieveModuli u v) : ℝ) ≤ N)
      (zero_le_one.trans hL)) (Real.rpow_nonneg (by linarith : 0 ≤ z) (4 * ((g : ℝ) + 1) * (1 + η) + δ))
  apply le_trans ?_ hlevel
  simpa only [mass_badSieveModuli, Nat.cast_mul, mul_assoc] using H'

end NairTenenbaum
