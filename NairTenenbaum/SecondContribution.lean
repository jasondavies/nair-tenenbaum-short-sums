module

public import NairTenenbaum.SecondContributionWeights
public import NairTenenbaum.MainTermLowerBound
public import NairTenenbaum.RealIntervalBounds

@[expose] public section

/-! # The small-crossing-prime contribution in the original interval -/

namespace NairTenenbaum

def PolynomialSystem.HasSmallCrossingPrime {k r : ℕ} (P : PolynomialSystem k r)
    (ε x : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧ q.Prime ∧
    (q : ℝ) ≤ x ^ ((P.total.natDegree : ℝ) * ε / 2) ∧
    (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ≤
      x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2) ∧
    x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) <
      (weightedMass P.exponent (primeSelect n (Finset.range (q + 1))) : ℝ)

noncomputable def PolynomialSystem.smallPrimeCrossingShortSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (ε x y : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (shortInterval x y).filter (fun n : ℕ => P.HasSmallCrossingPrime ε x n),
    extendArithmeticMap F (fun j => ((P.Q j).eval (n : ℤ)).natAbs)

theorem primePower_scale_identity (g : ℕ) (ε : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ((x ^ ((g : ℝ) * ε / 2)) ^ 3) ^ g = x ^ (3 * (g : ℝ) ^ 2 * ε / 2) := by
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

theorem PolynomialSystem.smallPrimeCrossingShortSum_le {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) {ε x : ℝ} (hε : 0 ≤ ε) (hx : 1 ≤ x) (y : ℝ) :
    P.smallPrimeCrossingShortSum F ε x y ≤
      P.primePowerContribution F (x ^ ((P.total.natDegree : ℝ) * ε / 2))
        (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
  classical
  let S := (shortInterval x y).filter (fun n : ℕ => P.HasSmallCrossingPrime ε x n)
  have hmap : ∀ t ∈ S, (t : ℤ) ∈ primePowerExceptionalSet P.R
      (x ^ ((P.total.natDegree : ℝ) * ε / 2)) ((x ^ ((P.total.natDegree : ℝ) * ε / 2)) ^ 3)
      (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
    intro t ht
    obtain ⟨ht, n, q, hn, hq, hqz, hs, hc⟩ := Finset.mem_filter.mp ht
    have hint : (t : ℤ) ∈ Finset.Ioc (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
      have H := Finset.mem_Ioc.mp ht
      exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast H.1, by exact_mod_cast H.2⟩
    apply P.mem_primePowerExceptionalSet_of_crossing hint hn hq
      (Real.rpow_nonneg (zero_le_one.trans hx) _) hqz
      (one_le_pow₀ (Real.one_le_rpow hx (by positivity)))
    · simpa only [primePower_scale_identity _ _ (zero_le_one.trans hx)] using hs
    · rw [primePower_scale_identity _ _ (zero_le_one.trans hx)]
      have heq : (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2)) ^ 2 =
          x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)]
        congr 1
        norm_num
      simpa only [heq] using hc
  exact Finset.sum_le_sum_of_injOn (fun n : ℕ => (n : ℤ))
    (fun _ _ _ _ h => Int.ofNat_inj.mp h) (Finset.image_subset_iff.mpr hmap) (fun _ _ => le_rfl)
    (fun t _ _ => extendArithmeticMap_nonneg hF _)

/-- At the paper's scales the modulus of every selected prime power fits in
the rounded interval once the prime cutoff reaches two. -/
theorem secondContribution_sieve_level {g : ℕ} (hg : 0 < g) {ε x y : ℝ}
    (hε : 0 < ε) (hx : 1 ≤ x) (hz : 2 ≤ x ^ ((g : ℝ) * ε / 2))
    (hy : x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y) :
    (x ^ ((g : ℝ) * ε / 2)) ^ 4 ≤ y / 2 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hz₄ : 2 ≤ (x ^ ((g : ℝ) * ε / 2)) ^ 4 := (by norm_num : (2 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hz 4)
  have heq : ((x ^ ((g : ℝ) * ε / 2)) ^ 4) ^ 2 = x ^ (4 * (g : ℝ) * ε) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)]
    congr 1
    norm_num
    ring
  have H : (4 * (g : ℝ) * ε) ≤ 4 * (g : ℝ) ^ 2 * ε := by
    nlinarith [mul_nonneg hε.le (mul_nonneg (show (0 : ℝ) ≤ g by positivity) (sub_nonneg.mpr hg₁))]
  have H' := (Real.rpow_le_rpow_of_exponent_le hx H).trans hy
  rw [← heq] at H'
  nlinarith

/-- The second-class estimate with the original height and interval hypotheses.
No normalization of `F(1)` is needed. -/
theorem exists_smallPrimeCrossingShortSum_theoremOne_bound {g : ℕ} (hg : 0 < g)
    {B ε δ : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (A : ℝ) (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      P.smallPrimeCrossingShortSum F ε x y ≤ C P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, hK, HK⟩ := exists_powerSaving_le_mainTerm g (by positivity : 0 < ε / 3)
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  let α : ℝ := (g : ℝ) * ε / 2
  have hα : 0 < α := by dsimp [α]; positivity
  let c₀ : ℝ := max 2 ((2 : ℝ) ^ (1 / α))
  let E : ℕ → ℝ := fun D => 8 * (g : ℝ) * (max g (D ^ 3) : ℕ) *
    (B * (((g : ℝ) + 1) * 2 ^ g) ^ (ε * δ / 3))
  have hE (D : ℕ) : 0 < E D := by
    have hM : (0 : ℝ) < (max g (D ^ 3) : ℕ) := by exact_mod_cast hg.trans_le (le_max_left _ _)
    dsimp [E]
    positivity
  have hc₀ : 2 ≤ c₀ := le_max_left _ _
  refine ⟨c₀, by linarith, (fun D => E D * K),
    (fun D => mul_pos (hE D) (lt_of_lt_of_le zero_lt_one hK)), ?_⟩
  intro k r P hdeg A F hF x y hx hy hyx
  have hH : (1 : ℝ) ≤ (polynomialHeight P.total : ℝ) := by
    exact_mod_cast polynomialHeight_pos P.total_ne_zero
  have hHδ : 1 ≤ (polynomialHeight P.total : ℝ) ^ δ := Real.one_le_rpow hH hδ.le
  have hcx : c₀ ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ c₀) hHδ).trans hx.le
  have hx₂ : 2 ≤ x := hc₀.trans hcx
  have hx₁ : 1 ≤ x := by linarith
  have hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x :=
    (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) δ) (by linarith : 1 ≤ c₀)).trans hx.le
  have hz : 2 ≤ x ^ α := by
    have H := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      ((le_max_right _ _).trans hcx) hα.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hα.ne', Real.rpow_one] at H
    exact H
  have hz₁ : 1 ≤ x ^ α := by linarith
  have hlevel := secondContribution_sieve_level hg hε hx₁ hz hy
  have hy₂ : 2 ≤ y := by
    have H := one_le_pow₀ (n := 4) hz₁
    linarith
  obtain ⟨hab, hlength, hlength', hinterval⟩ := shortInterval_endpoint_bounds (by linarith) hy₂ hyx
  have Hraw := P.primePowerContribution_power_saving hdeg hg hF (zero_le_one.trans hB)
    hε hδ hδ₁ hx₁ hz₁ hheight hab (hlevel.trans hlength) hlength' hinterval
  have Hfirst := P.smallPrimeCrossingShortSum_le hF.nonneg hε.le hx₁ y
  rw [hdeg] at Hfirst
  have H := Hfirst.trans Hraw
  have H' := mul_le_mul_of_nonneg_left (HK k r P hdeg.le F hF.nonneg x y hx₂ (by linarith))
    (hE P.badDiscriminant).le
  apply H.trans
  dsimp only [E] at H'
  simpa only [E, mul_assoc] using H'

/-- The first-crossing class in the proof is a subclass of this majorant. -/
theorem PolynomialSystem.sum_subclass_le_smallPrimeCrossingShortSum {k r : ℕ}
    (P : PolynomialSystem k r) {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n)
    (ε x y : ℝ) (S : Finset ℕ) (hS : S ⊆ shortInterval x y)
    (hcross : ∀ n ∈ S, P.HasSmallCrossingPrime ε x n) :
    (∑ n ∈ S, extendArithmeticMap F (fun j => ((P.Q j).eval (n : ℤ)).natAbs)) ≤
      P.smallPrimeCrossingShortSum F ε x y := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_filter.mpr ⟨hS hn, hcross n hn⟩
  · intro _ _ _
    exact extendArithmeticMap_nonneg hF _

end NairTenenbaum
