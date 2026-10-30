module

public import NairTenenbaum.IntermediateContribution
public import NairTenenbaum.RealIntervalBounds

@[expose] public section

/-! # The intermediate-prefix bound in the original real short interval -/

namespace NairTenenbaum

def PolynomialSystem.HasIntermediatePrefixReal {k r : ℕ} (P : PolynomialSystem k r)
    (T X w₀ x u : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧
    (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ≤ T ∧
    X < (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ∧
    (∀ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors → (p : ℝ) ≤ x ^ u) ∧
    ∃ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors ∧ w₀ < (p : ℝ)

noncomputable def PolynomialSystem.intermediatePrefixShortSum {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (ε w₀ x y : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (shortInterval x y).filter (fun n : ℕ => P.HasIntermediatePrefixReal
      (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε))
      (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2)) w₀ x
      ((P.total.natDegree : ℝ) * ε / 16) n),
    extendArithmeticMap F (fun j => ((P.Q j).eval (n : ℤ)).natAbs)

theorem PolynomialSystem.hasIntermediatePrefixReal_iff {k r : ℕ} (P : PolynomialSystem k r)
    {T : ℝ} (hT : 1 ≤ T) (X w₀ x u : ℝ) (t : ℤ) :
    P.HasIntermediatePrefixReal T X w₀ x u t ↔
      P.HasIntermediatePrefix (Nat.toPNat' ⌊T⌋₊) X w₀ x u t := by
  simp only [HasIntermediatePrefixReal, HasIntermediatePrefix,
    PNat.toPNat'_coe (Nat.floor_pos.mpr hT), Nat.le_floor_iff (zero_le_one.trans hT)]

theorem PolynomialSystem.intermediatePrefixShortSum_eq {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (ε w₀ x y : ℝ)
    (hT : 1 ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)) :
    P.intermediatePrefixShortSum F ε w₀ x y = P.intermediatePrefixContribution F
      (Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊)
      (x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε / 2)) w₀ x
      ((P.total.natDegree : ℝ) * ε / 16) (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
  classical
  unfold intermediatePrefixShortSum intermediatePrefixContribution
  rw [← shortInterval_natCast_image]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    rw [P.hasIntermediatePrefixReal_iff hT]
  · exact fun _ _ _ _ h => Int.ofNat_inj.mp h

/-- The intermediate contribution at the real cutoffs, with all endpoint
rounding and polynomial-value bounds discharged. -/
theorem exists_intermediatePrefixShortSum_bound {g : ℕ} (hg : 0 < g)
    {ε δ A : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hδ : 0 < δ) (hA : 1 ≤ A) :
    ∃ K x₀ κ w₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ 0 < κ ∧ 1 < w₀ ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (B σ : ℝ) (F : ArithmeticMap k), Admissible A B σ F → 1 ≤ B → 0 < σ →
      (g : ℝ) ^ 2 * σ ≤ 1 / 8 → ∀ x y : ℝ, x₀ ≤ x →
      (polynomialHeight P.total : ℝ) ^ δ ≤ x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      P.intermediatePrefixShortSum F ε w₀ x y ≤
        K * smoothTailSieveCost A B κ g P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, x₁, κ, w₀, hK, hx₁, hκ, hw₀, H⟩ :=
    exists_intermediatePrefixContribution_mainTerm_bound hg hε hsmall hδ hA
  let β : ℝ := 4 * (g : ℝ) ^ 2 * ε
  have hβ : 0 < β := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    dsimp [β]
    positivity
  refine ⟨K, max x₁ ((2 : ℝ) ^ (1 / β)), κ, w₀, hK,
    hx₁.trans_le (le_max_left _ _), hκ, hw₀, ?_⟩
  intro k r P hdeg B σ F hF hB hσ hσsmall x y hx hheight hy hyx
  have hx₁' : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx' : 1 < x := hx₁.trans_le hx₁'
  have hy₂ : 2 ≤ y := by
    have Hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      ((le_max_right _ _).trans hx) hβ.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hβ.ne', Real.rpow_one] at Hpow
    exact Hpow.trans hy
  obtain ⟨hab, hlength, hlength', hinterval⟩ := shortInterval_endpoint_bounds (by linarith) hy₂ hyx
  have hT : 1 ≤ x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε) :=
    Real.one_le_rpow hx'.le (by positivity)
  rw [P.intermediatePrefixShortSum_eq F ε w₀ x y hT]
  have hN : ((Nat.toPNat' ⌊x ^ (3 * (P.total.natDegree : ℝ) ^ 2 * ε)⌋₊ : ℕ+) : ℝ) ≤
      x ^ (3 * (g : ℝ) ^ 2 * ε) := by
    rw [PNat.toPNat'_coe (Nat.floor_pos.mpr hT), hdeg]
    exact Nat.floor_le (by positivity)
  simpa only [hdeg, Int.cast_natCast] using H k r P hdeg B σ F hF hB hσ hσsmall x y _
    (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) hx₁' hheight hN hy hab hlength hlength' hinterval

/-- The intermediate-prime contribution with exactly Theorem 1's height and
arithmetic growth hypotheses. The fixed lower prime cutoff is independent of
the polynomial family and its restricted discriminant. -/
theorem exists_intermediatePrefixShortSum_theoremOne_bound {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ w₀ : ℝ, 0 < c₀ ∧ 1 < w₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      P.intermediatePrefixShortSum F ε w₀ x y ≤ C P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, x₀, κ, w₀, hK, hx₀, _, hw₀, H⟩ :=
    exists_intermediatePrefixShortSum_bound hg hε hsmall hδ hA
  let C : ℕ → ℝ := fun D => K * smoothTailSieveCost A B κ g (max 1 D)
  have hC (D : ℕ) : 0 < C D := mul_pos hK (smoothTailSieveCost_pos
    (lt_of_lt_of_le zero_lt_one hB) hg (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))
  refine ⟨x₀, w₀, by linarith, hw₀, C, hC, ?_⟩
  intro k r P hdeg F hF x y hx hy hyx
  have hH : (1 : ℝ) ≤ (polynomialHeight P.total : ℝ) := by
    exact_mod_cast polynomialHeight_pos P.total_ne_zero
  have hHδ : 1 ≤ (polynomialHeight P.total : ℝ) ^ δ := Real.one_le_rpow hH hδ.le
  have hx₀' : x₀ ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ x₀) hHδ).trans hx.le
  have hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x :=
    (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) δ) hx₀.le).trans hx.le
  have hσ : 0 < ε * δ / 3 := by positivity
  have hσε : ε * δ / 3 ≤ ε := by nlinarith
  have hσsmall : (g : ℝ) ^ 2 * (ε * δ / 3) ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hσε (sq_nonneg _)).trans hsmall
  have HD : max 1 P.badDiscriminant = P.badDiscriminant := max_eq_right P.badDiscriminant_pos
  simpa only [C, HD] using H k r P hdeg B (ε * δ / 3) F hF hB hσ hσsmall x y hx₀' hheight hy hyx

end NairTenenbaum
