module

public import NairTenenbaum.FirstContribution
public import NairTenenbaum.LargePrefixMainTerm

@[expose] public section

/-! # Prefixes up to the larger mass cutoff with a rough remainder -/

namespace NairTenenbaum

/-- Uniform main-term bound for prefixes with a rough remainder. The height hypothesis
and elementary interval bounds discharge the polynomial-value estimate. -/
theorem exists_largeRoughContribution_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε δ A : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hδ : 0 < δ) (hA : 1 ≤ A) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → ∀ (B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (polynomialHeight P.total : ℝ) ^ δ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, (t.natAbs : ℝ) ≤ 2 * x) →
      P.smallRoughContribution F N a b (x ^ ((g : ℝ) * ε / 16)) ≤
        K * smallDivisorSieveCost B σ g P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, x₁, hK, hx₁, H⟩ := exists_largePrefixSiftedSum_mainTerm_bound hg hε hsmall
  let C := A ^ (((g : ℝ) + 1 / δ + 1) / ((g : ℝ) * ε / 16))
  have hC : 0 < C := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hA) _
  refine ⟨C * K, max x₁ (max 2 (((g : ℝ) + 1) * 2 ^ g)), mul_pos hC hK,
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro k r P hdeg B σ F hF hB hσ hσsmall x y N a b hx hheight hN hy hab hlength hlength' hinterval
  have hx₂ : 2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hlarge : ((g : ℝ) + 1) * 2 ^ g ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hα : 0 < (g : ℝ) * ε / 16 := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  have H' := P.smallRoughContribution_le hF hA (zero_le_one.trans hB) N a b
    (by linarith : 1 < x) hα (fun t ht => eval_natAbs_le_rpow_of_height hdeg
      (by linarith) hδ hheight hlarge (hinterval t ht))
  have H'' := mul_le_mul_of_nonneg_left
    (H k r P hdeg A B σ F hF (zero_le_one.trans hA) hB hσ hσsmall x y N a b
      ((le_max_left _ _).trans hx) hN hy hab hlength hlength') hC.le
  exact H'.trans (by simpa only [C, mul_assoc] using H'')

end NairTenenbaum
