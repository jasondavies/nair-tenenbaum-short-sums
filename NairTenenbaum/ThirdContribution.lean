module

public import NairTenenbaum.ThirdContributionWeights
public import NairTenenbaum.MainTermLowerBound
public import NairTenenbaum.RealIntervalBounds

@[expose] public section

/-! # Large prefixes on a fixed finite prime support

A divisor-tuple majorant covers the third class. Its proof uses a single
smooth divisor of the radical value and does not remove any bad-prime powers.
-/

namespace NairTenenbaum

def PolynomialSystem.HasLargeSmoothDivisorTuple {k r : ℕ} (P : PolynomialSystem k r)
    (s : Finset ℕ) (ε x : ℝ) (t : ℤ) : Prop :=
  ∃ m : Tuple r, (∀ i, (m i : ℤ) ∣ (P.R i).eval t) ∧
    weightedMass P.exponent m ∈ Nat.factoredNumbers s ∧
    x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2) < (weightedMass P.exponent m : ℝ) ∧
    (weightedMass P.exponent m : ℝ) ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)

noncomputable def PolynomialSystem.largeSmoothShortSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (s : Finset ℕ) (ε x y : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (shortInterval x y).filter (fun n : ℕ => P.HasLargeSmoothDivisorTuple s ε x n),
    extendArithmeticMap F (fun j => ((P.Q j).eval (n : ℤ)).natAbs)

/-- The third-class divisor-tuple majorant is bounded by the smooth-divisor
exceptional sum, with no coprimality restriction on the tuple. -/
theorem PolynomialSystem.largeSmoothShortSum_le {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (s : Finset ℕ)
    {ε x : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) (y : ℝ) :
    P.largeSmoothShortSum F s ε x y ≤ P.smoothDivisorContribution F s
      (Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊)
      (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)) (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
  classical
  let S := (shortInterval x y).filter (fun n : ℕ => P.HasLargeSmoothDivisorTuple s ε x n)
  have hxN : 1 ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) := Real.one_le_rpow hx (by positivity)
  have hmap : ∀ t ∈ S, (t : ℤ) ∈ smoothDivisorExceptionalSet P.radical s
      (Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊)
      (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)) (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
    intro t ht
    obtain ⟨ht, m, hdiv, hsmooth, hlarge, hsmall⟩ := Finset.mem_filter.mp ht
    have hint : (t : ℤ) ∈ Finset.Ioc (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
      have H := Finset.mem_Ioc.mp ht
      exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast H.1, by exact_mod_cast H.2⟩
    apply P.mem_smoothDivisorExceptionalSet_of_tuple s _ hint m hdiv hsmooth
    · have heq : (x ^ (3 * (P.total.natDegree : ℝ) * ε / 2)) ^ P.total.natDegree =
          x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)]
        congr 1
        ring
      simpa only [heq] using hlarge
    · rw [PNat.toPNat'_coe (Nat.floor_pos.mpr hxN)]
      exact (Nat.le_floor_iff (zero_le_one.trans hxN)).mpr hsmall
  exact Finset.sum_le_sum_of_injOn (fun n : ℕ => (n : ℤ))
    (fun _ _ _ _ h => Int.ofNat_inj.mp h) (Finset.image_subset_iff.mpr hmap) (fun _ _ => le_rfl)
    (fun t _ _ => extendArithmeticMap_nonneg hF _)

/-- The large-divisor upper cutoff is below half the available interval. -/
theorem largeDivisor_sieve_level {g : ℕ} {ε x y : ℝ} (hx : 0 < x)
    (hgap : 2 ≤ x ^ ((g : ℝ) ^ 2 * ε)) (hy : x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y) :
    x ^ (3 * (g : ℝ) ^ 2 * ε) ≤ y / 2 := by
  have H := mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hx.le (3 * (g : ℝ) ^ 2 * ε))
  rw [← Real.rpow_add hx] at H
  have heq : (g : ℝ) ^ 2 * ε + 3 * (g : ℝ) ^ 2 * ε = 4 * (g : ℝ) ^ 2 * ε := by ring
  rw [heq] at H
  linarith

/-- The third-class estimate with a threshold independent of the finite prime
support. Its upper-bound constant may depend on that support and on `D`. -/
theorem exists_largeSmoothShortSum_theoremOne_bound {g : ℕ} (hg : 0 < g)
    {B ε δ : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ s : Finset ℕ, ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (A : ℝ) (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      P.largeSmoothShortSum F s ε x y ≤ C P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, hK, HK⟩ := exists_powerSaving_le_mainTerm g (by positivity : 0 < ε / 12)
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  let α : ℝ := (g : ℝ) ^ 2 * ε
  have hα : 0 < α := by dsimp [α]; positivity
  let c₀ : ℝ := max 2 ((2 : ℝ) ^ (1 / α))
  have hc₀ : 2 ≤ c₀ := le_max_left _ _
  refine ⟨c₀, by linarith, ?_⟩
  intro s
  let E : ℕ → ℝ := fun D => 4 * smoothDivisorBound g (max 1 D) s *
    (B * (((g : ℝ) + 1) * 2 ^ g) ^ (ε * δ / 3))
  have hE (D : ℕ) : 0 < E D := by
    have HM := smoothDivisorBound_pos g (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 D)) s
    dsimp [E]
    positivity
  refine ⟨fun D => E D * K, fun D => mul_pos (hE D) (lt_of_lt_of_le zero_lt_one hK), ?_⟩
  intro k r P hdeg A F hF x y hx hy hyx
  have hH : (1 : ℝ) ≤ (polynomialHeight P.total : ℝ) := by exact_mod_cast polynomialHeight_pos P.total_ne_zero
  have hHδ : 1 ≤ (polynomialHeight P.total : ℝ) ^ δ := Real.one_le_rpow hH hδ.le
  have hcx : c₀ ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ c₀) hHδ).trans hx.le
  have hx₂ : 2 ≤ x := hc₀.trans hcx
  have hx₁ : 1 ≤ x := by linarith
  have hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x :=
    (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) δ) (by linarith : 1 ≤ c₀)).trans hx.le
  have hgap : 2 ≤ x ^ α := by
    have H := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      ((le_max_right _ _).trans hcx) hα.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hα.ne', Real.rpow_one] at H
    exact H
  have hlevel := largeDivisor_sieve_level (by linarith : 0 < x) hgap hy
  have hcut : 1 ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) := Real.one_le_rpow hx₁ (by positivity)
  have hy₂ : 2 ≤ y := by linarith
  obtain ⟨hab, hlength, hlength', hinterval⟩ := shortInterval_endpoint_bounds (by linarith) hy₂ hyx
  let N := Nat.toPNat' ⌊x ^ (3 * (g : ℝ) ^ 2 * ε)⌋₊
  have hN : (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) := by
    dsimp only [N]
    rw [PNat.toPNat'_coe (Nat.floor_pos.mpr hcut)]
    exact Nat.floor_le (zero_le_one.trans hcut)
  have Hraw := P.smoothDivisorContribution_power_saving hdeg hg hF (zero_le_one.trans hB)
    hε hδ hδ₁ hx₁ hheight s N hab ((hN.trans hlevel).trans hlength) hlength' hinterval
  have Hfirst := P.largeSmoothShortSum_le hF.nonneg s hε.le hx₁ y
  rw [hdeg] at Hfirst
  have H := Hfirst.trans Hraw
  have H' := mul_le_mul_of_nonneg_left (HK k r P hdeg.le F hF.nonneg x y hx₂ (by linarith))
    (hE P.badDiscriminant).le
  have HD : max 1 P.badDiscriminant = P.badDiscriminant := max_eq_right P.badDiscriminant_pos
  apply H.trans
  simpa only [E, HD, mul_assoc] using H'

/-- Any third class selected by the prefix decomposition is bounded by this
more general divisor-tuple contribution. -/
theorem PolynomialSystem.sum_subclass_le_largeSmoothShortSum {k r : ℕ}
    (P : PolynomialSystem k r) {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n)
    (s : Finset ℕ) (ε x y : ℝ) (S : Finset ℕ) (hS : S ⊆ shortInterval x y)
    (hdiv : ∀ n ∈ S, P.HasLargeSmoothDivisorTuple s ε x n) :
    (∑ n ∈ S, extendArithmeticMap F (fun j => ((P.Q j).eval (n : ℤ)).natAbs)) ≤
      P.largeSmoothShortSum F s ε x y := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_filter.mpr ⟨hS hn, hdiv n hn⟩
  · intro _ _ _
    exact extendArithmeticMap_nonneg hF _

end NairTenenbaum
