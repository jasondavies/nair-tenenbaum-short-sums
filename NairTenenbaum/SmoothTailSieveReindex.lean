module

public import NairTenenbaum.SmallDivisorSum
public import NairTenenbaum.SplitSmoothTail

@[expose] public section

/-! # Reindexing the original smooth mass tail under the sieve restriction -/

namespace NairTenenbaum

noncomputable def smoothTailDivisorTuples {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (N : ℕ+) (s : Finset ℕ) (X : ℝ) : Finset (Tuple r) := by
  classical
  exact (smallDivisorTuples γ N).filter (fun m =>
    (∀ i, (m i : ℕ) ∈ Nat.factoredNumbers s) ∧ X < (weightedMass γ m : ℝ))

noncomputable def PolynomialSystem.smoothTailSiftedSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (s : Finset ℕ) (X : ℝ) (a b : ℤ) (z : ℝ) : ℝ :=
  ∑ m ∈ smoothTailDivisorTuples P.exponent N s X, pullback P.exponent F m *
    conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass m) z) P.R m a b

/-- The combined mass tail survives full bad-prime splitting unchanged.
Only positive-count tuples require a witness for the discriminant conditions. -/
theorem PolynomialSystem.smoothTailSiftedSum_le_split {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (s : Finset ℕ) (X : ℝ)
    (a b : ℤ) (z : ℝ) :
    P.smoothTailSiftedSum F N s X a b z ≤
      ∑ v ∈ smoothWeightUpTo P.exponent P.discriminant s N,
        ∑ u ∈ (smallBadParts P.exponent P.badDiscriminant v N).filter
            (fun u => X < (weightedMass P.exponent (u * v) : ℝ)),
          pullback P.exponent F (u * v) * P.badPrimeSiftedCount u v a b z := by
  classical
  let count := fun m => conditionalPolynomialSiftedCount P.total (sieveModulus P.total (mass m) z) P.R m a b
  let T := (smoothTailDivisorTuples P.exponent N s X).filter (fun m => count m ≠ 0)
  let f : Tuple r → ℝ := fun m => pullback P.exponent F m * count m
  let e : Tuple r → (Σ _v : Tuple r, Tuple r) := fun m =>
    ⟨primeReject m P.discriminant.primeFactors, primeSelect m P.discriminant.primeFactors⟩
  let V := (smoothWeightUpTo P.exponent P.discriminant s N).sigma (fun v =>
    (smallBadParts P.exponent P.badDiscriminant v N).filter (fun u => X < (weightedMass P.exponent (u * v) : ℝ)))
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
    obtain ⟨hm, hsmooth, hlarge⟩ := Finset.mem_filter.mp hm
    have hmass := (Finset.mem_filter.mp hm).2
    have hcpos : 0 < count m := Nat.pos_of_ne_zero hc
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hcpos
    have hdiv : ∀ i, (m i : ℕ) ∣ ((P.R i).eval n).natAbs := by
      have H := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      intro i
      exact Int.natCast_dvd.mp (H i)
    apply Finset.mem_sigma.mpr
    constructor
    · apply (mem_smoothWeightUpTo P.exponent P.exponent_pos P.discriminant s N _).mpr
      refine ⟨⟨?_, P.divisor_primeReject_dagger n m hdiv⟩, ?_⟩
      · have H := Nat.le_mul_of_pos_left (weightedMass P.exponent (e m).1)
          (weightedMass_pos P.exponent (e m).2)
        rw [← weightedMass_mul, heprod] at H
        exact H.trans hmass
      · intro i
        exact Nat.mem_factoredNumbers_of_dvd (hsmooth i) (primeReject_coordinate_dvd m _ i)
    · apply Finset.mem_filter.mpr
      refine ⟨?_, by simpa only [heprod] using hlarge⟩
      apply (mem_smallBadParts P.exponent P.exponent_pos P.badDiscriminant _ _ N).mpr
      refine ⟨P.divisor_primeSelect_bad_support n m hdiv, ?_⟩
      simpa only [heprod] using hmass
  have hew (m : Tuple r) : f m = w (e m) := by
    dsimp only [f, w, count]
    rw [heprod]
    unfold PolynomialSystem.badPrimeSiftedCount
    rw [sieveModulus_badSieveModuli, heprod]
  have hrestrict : P.smoothTailSiftedSum F N s X a b z = ∑ m ∈ T, f m := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hnot
    have hc : count m = 0 := by by_contra h; exact hnot (Finset.mem_filter.mpr ⟨hm, h⟩)
    simp only [f, hc, Nat.cast_zero, mul_zero]
  rw [hrestrict]
  have H := Finset.sum_le_sum_of_injOn e heinj.injOn himage (fun m _ => (hew m).le)
    (fun t _ _ => mul_nonneg (hF _) (Nat.cast_nonneg _))
  simpa only [V, w, Finset.sum_sigma] using H

end NairTenenbaum
