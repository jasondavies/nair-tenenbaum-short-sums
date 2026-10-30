module

public import NairTenenbaum.SmallDivisorSieve

@[expose] public section

/-! # Small polynomial divisor sums in the original tuple variables

Whole-prime-power splitting reindexes the original divisor tuples into good
and bad parts. Tuples with zero congruence count contribute zero; all remaining
tuples inherit the required discriminant coprimality from an actual value.
-/

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem mass_dvd_weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (m : Tuple r) : mass m ∣ weightedMass γ m :=
  Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => dvd_pow_self _ (hγ i).ne')

theorem mass_badSieveModuli_le_weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (u v : Tuple r) :
    mass (badSieveModuli u v) ≤ weightedMass γ (u * v) := by
  apply Nat.le_of_dvd (weightedMass_pos γ (u * v))
  apply dvd_trans _ (mass_dvd_weightedMass γ hγ (u * v))
  rw [mass_badSieveModuli, mass_mul]
  exact mul_dvd_mul_right (tupleLCM_dvd_mass u) (mass v)

theorem prime_dvd_mass_iff_tupleLCM {r : ℕ} (u : Tuple r) {p : ℕ} (hp : p.Prime) :
    p ∣ mass u ↔ p ∣ tupleLCM u := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff (fun i => (u i : ℕ))).mp h
    exact hi.trans (coordinate_dvd_tupleLCM u i)
  · exact fun h => h.trans (tupleLCM_dvd_mass u)

theorem sieveModulus_badSieveModuli {r : ℕ} (Q : ℤ[X]) (u v : Tuple r) (z : ℝ) :
    sieveModulus Q (mass (badSieveModuli u v)) z = sieveModulus Q (mass (u * v)) z := by
  unfold sieveModulus
  congr 1
  ext p
  by_cases hp : p.Prime
  · simp only [sievePrimeSet, Finset.mem_filter, Finset.mem_range, hp, and_true,
      mass_badSieveModuli, mass_mul, hp.dvd_mul, prime_dvd_mass_iff_tupleLCM u hp]
  · simp [sievePrimeSet, hp]

noncomputable def smallDivisorTuples {k r : ℕ} (γ : Fin k → Fin r → ℕ) (N : ℕ+) : Finset (Tuple r) :=
  (tupleBox r N).filter (fun m => weightedMass γ m ≤ N)

noncomputable def smallBadParts {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ) (v : Tuple r) (N : ℕ+) : Finset (Tuple r) :=
  (tupleBox r N).filter (fun u => (∀ i, (u i : ℕ) ∈ Nat.factoredNumbers D.primeFactors) ∧ weightedMass γ (u * v) ≤ N)

theorem mem_smallBadParts {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (u v : Tuple r) (N : ℕ+) :
    u ∈ smallBadParts γ D v N ↔
      (∀ i, (u i : ℕ) ∈ Nat.factoredNumbers D.primeFactors) ∧ weightedMass γ (u * v) ≤ N := by
  classical
  simp only [smallBadParts, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  apply mem_tupleBox.mpr
  intro i
  have H : (u i : ℕ) ≤ ((u * v) i : ℕ) := by
    simpa only [Pi.mul_apply, PNat.mul_coe] using Nat.le_mul_of_pos_right (u i : ℕ) (v i).pos
  exact H.trans ((coordinate_le_weightedMass γ hγ (u * v) i).trans h.2)

noncomputable def PolynomialSystem.smallDivisorSiftedSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (a b : ℤ) (z : ℝ) : ℝ :=
  ∑ m ∈ smallDivisorTuples P.exponent N, pullback P.exponent F m *
    conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass m) z) P.R m a b

theorem PolynomialSystem.smallDivisorSiftedSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (a b : ℤ) (z : ℝ) :
    P.smallDivisorSiftedSum F N a b z ≤
      ∑ v ∈ weightUpTo P.exponent P.discriminant N,
        ∑ u ∈ smallBadParts P.exponent P.badDiscriminant v N,
          pullback P.exponent F (u * v) * P.badPrimeSiftedCount u v a b z := by
  classical
  let count := fun m => conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass m) z) P.R m a b
  let T := (smallDivisorTuples P.exponent N).filter (fun m => count m ≠ 0)
  let f : Tuple r → ℝ := fun m => pullback P.exponent F m * count m
  let e : Tuple r → (Σ _v : Tuple r, Tuple r) := fun m =>
    ⟨primeReject m P.discriminant.primeFactors, primeSelect m P.discriminant.primeFactors⟩
  let V := (weightUpTo P.exponent P.discriminant N).sigma (fun v => smallBadParts P.exponent P.badDiscriminant v N)
  let w : (Σ _v : Tuple r, Tuple r) → ℝ := fun t =>
    pullback P.exponent F (t.2 * t.1) * P.badPrimeSiftedCount t.2 t.1 a b z
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
    unfold PolynomialSystem.badPrimeSiftedCount
    rw [sieveModulus_badSieveModuli, heprod]
  have hrestrict : P.smallDivisorSiftedSum F N a b z = ∑ m ∈ T, f m := by
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
theorem exists_smallDivisorSiftedSum_bound {g : ℕ} (hg : 0 < g) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K L : ℝ, 1 ≤ K ∧ 1 ≤ L ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (A B ε : ℝ) (F : ArithmeticMap k), Admissible A B ε F → 0 ≤ A → 1 ≤ B → 0 < ε →
      (g : ℝ) ^ 2 * ε ≤ 1 / 8 →
      ∀ (N : ℕ+) (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      L * (N : ℝ) * z ^ (4 * (g : ℝ) * (1 + η) + δ) ≤ (b : ℝ) - a →
      P.smallDivisorSiftedSum F N a b z ≤
        K * smallDivisorSieveCost B ε g P.badDiscriminant * ((b : ℝ) - a) * sieveProduct P.total z *
          ∑ n ∈ Finset.Icc 1 N, P.weight F n := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_smallDivisor_sieve_sum_bound hg hη hδ
  refine ⟨K, L, hK, hL, ?_⟩
  intro k r P hdeg A B ε F hF hA hB hε hsmall N a b z hab hz hzlog hlevel
  refine (P.smallDivisorSiftedSum_le_split hF.nonneg N a b z).trans ?_
  apply H k r P hdeg A B ε F hF hA hB hε hsmall N
    (fun v => smallBadParts P.exponent P.badDiscriminant v N)
    (fun v _ u hu => ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).1)
    a b z hab hz hzlog
  intro v _ u hu
  have huN := ((mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant u v N).mp hu).2
  have hmod := (mass_badSieveModuli_le_weightedMass P.exponent P.exponent_pos u v).trans huN
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmod : (mass (badSieveModuli u v) : ℝ) ≤ N)
      (zero_le_one.trans hL)) (Real.rpow_nonneg (by linarith : 0 ≤ z) (4 * (g : ℝ) * (1 + η) + δ))
  apply le_trans ?_ hlevel
  simpa only [mass_badSieveModuli, Nat.cast_mul, mul_assoc] using H'

end NairTenenbaum
