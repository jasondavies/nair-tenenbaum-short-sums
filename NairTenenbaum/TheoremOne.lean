module

public import NairTenenbaum.ShortSumDecomposition
public import NairTenenbaum.Targets

@[expose] public section

/-! # Theorem 1: short sums of admissible arithmetic functions

The four majorants give a coefficient-independent height threshold and a bound
constant depending only on the fixed parameters and the restricted discriminant.
The bad-prime corrections retain all valuations throughout the proof.
-/

namespace NairTenenbaum

/-- The short-sum estimate, with constants uniform also in the number of
polynomials and irreducible factors at fixed total degree. -/
theorem exists_shortSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      shortSum P.Q F x y ≤ C P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨c₁, _, C₁, hC₁, H₁⟩ := exists_largeRoughShortSum_theoremOne_bound hg hA hB hε hsmall hδ hδ₁
  obtain ⟨c₂, _, C₂, hC₂, H₂⟩ := exists_smallPrimeCrossingShortSum_theoremOne_bound hg hB hε hδ hδ₁
  obtain ⟨c₃, _, H₃⟩ := exists_largeSmoothShortSum_theoremOne_bound hg hB hε hδ hδ₁
  obtain ⟨c₄, w₀, _, hw₀, C₄, hC₄, H₄⟩ :=
    exists_intermediatePrefixShortSum_theoremOne_bound hg hA hB hε hsmall hδ hδ₁
  obtain ⟨C₃, hC₃, H₃⟩ := H₃ (Finset.Icc 0 ⌊w₀⌋₊)
  let c₀ := max 1 (max c₁ (max c₂ (max c₃ c₄)))
  have hc₀ : 1 ≤ c₀ := le_max_left _ _
  have hc₁ : c₁ ≤ c₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hc₂ : c₂ ≤ c₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hc₃ : c₃ ≤ c₀ := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have hc₄ : c₄ ≤ c₀ := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨c₀, by linarith, fun D => C₁ D + C₂ D + C₃ D + C₄ D,
    fun D => add_pos (add_pos (add_pos (hC₁ D) (hC₂ D)) (hC₃ D)) (hC₄ D), ?_⟩
  intro k r P hdeg F hF x y hx hy hyx
  have hH : (1 : ℝ) ≤ (polynomialHeight P.total : ℝ) := by
    exact_mod_cast polynomialHeight_pos P.total_ne_zero
  have hHδ : 1 ≤ (polynomialHeight P.total : ℝ) ^ δ := Real.one_le_rpow hH hδ.le
  have hx₁ : 1 ≤ x := hc₀.trans
    ((le_mul_of_one_le_right (zero_le_one.trans hc₀) hHδ).trans hx.le)
  have hheight₀ : 0 ≤ (polynomialHeight P.total : ℝ) ^ δ := zero_le_one.trans hHδ
  have Hrough := H₁ k r P hdeg F hF x y ((mul_le_mul_of_nonneg_right hc₁ hheight₀).trans_lt hx) hy hyx
  have Hprime := H₂ k r P hdeg A F hF x y ((mul_le_mul_of_nonneg_right hc₂ hheight₀).trans_lt hx) hy hyx
  have Hsmooth := H₃ k r P hdeg A F hF x y ((mul_le_mul_of_nonneg_right hc₃ hheight₀).trans_lt hx) hy hyx
  have Hmiddle := H₄ k r P hdeg F hF x y ((mul_le_mul_of_nonneg_right hc₄ hheight₀).trans_lt hx) hy hyx
  apply (P.shortSum_le_four_contributions hF.nonneg hε.le hx₁ hw₀.le y).trans
  simpa only [add_mul] using add_le_add (add_le_add (add_le_add Hrough Hprime) Hsmooth) Hmiddle

/-- Theorem 1, equation (18), with the quantifier order recorded in `Targets`.
This is a proof of the original target proposition, not an additional hypothesis. -/
theorem theoremOne : TheoremOne := by
  intro k r g _ _ hg A B ε δ hA hB hε hsmall hδ hδ₁
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hsmall' : (g : ℝ) ^ 2 * ε ≤ 1 / 8 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * (g : ℝ) ^ 2)).mp hsmall
    nlinarith
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_shortSum_mainTerm_bound hg hA hB hε hsmall' hδ hδ₁
  exact ⟨c₀, hc₀, C, hC, H k r⟩

end NairTenenbaum
