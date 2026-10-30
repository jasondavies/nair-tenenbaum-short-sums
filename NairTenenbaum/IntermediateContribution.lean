module

public import NairTenenbaum.PrimeBandCover
public import NairTenenbaum.PolynomialValueBounds

@[expose] public section

/-! # Uniform bound for the intermediate-prime prefix contribution -/

namespace NairTenenbaum

/-- The entire middle range of largest prefix primes is bounded, with the
polynomial-value growth supplied by the height hypothesis. All constants and
the fixed lower prime cutoff are chosen before the polynomial family. -/
theorem exists_intermediatePrefixContribution_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε δ A : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hδ : 0 < δ) (hA : 1 ≤ A) :
    ∃ K x₀ κ w₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ 0 < κ ∧ 1 < w₀ ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (B σ : ℝ) (F : ArithmeticMap k), Admissible A B σ F → 1 ≤ B → 0 < σ →
      (g : ℝ) ^ 2 * σ ≤ 1 / 8 → ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (polynomialHeight P.total : ℝ) ^ δ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, (t.natAbs : ℝ) ≤ 2 * x) →
      P.intermediatePrefixContribution F N (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) w₀ x
        ((g : ℝ) * ε / 16) a b ≤
        K * smoothTailSieveCost A B κ g P.badDiscriminant * mainTerm P F x y := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hu : 0 < (g : ℝ) * ε / 16 := by positivity
  have hu₁ : (g : ℝ) * ε / 16 ≤ 1 := by
    nlinarith [mul_nonneg hε.le (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
      (sub_nonneg.mpr hg₁))]
  obtain ⟨K, x₁, κ, w₀, hK, hx₁, hκ, hw₀, H⟩ := exists_largePrefixBands_mainTerm_bound
    hg hε hA (by positivity : 0 ≤ (g : ℝ) + 1 / δ + 1)
  let x₀ : ℝ := max x₁ (max (Real.exp 1) (((g : ℝ) + 1) * 2 ^ g))
  have hxx₀ : Real.exp 1 ≤ x₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hx₀ : 1 < x₀ := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hxx₀
  refine ⟨K, x₀, κ, w₀, hK, hx₀, hκ, hw₀, ?_⟩
  intro k r P hdeg B σ F hF hB hσ hσsmall x y N a b hxx hheight hN hy hab hlen hlen' hinterval
  have hx : 1 < x := hx₀.trans_le hxx
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hxx₀.trans hxx)
  have hlarge : ((g : ℝ) + 1) * 2 ^ g ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hxx)
  obtain ⟨J, hJ, HJ⟩ := P.intermediatePrefixContribution_le_bands hF.nonneg N
    (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) w₀ x ((g : ℝ) * ε / 16) a b hx hw₀.le
  exact HJ.trans (H k r P hdeg B σ F hF hB hσ hσsmall x y ((g : ℝ) * ε / 16) N a b J
    ((le_max_left _ _).trans hxx) hx hlog hu hu₁ le_rfl (fun j hj => (hJ j hj).le)
    hN hy hab hlen hlen' (fun t ht => eval_natAbs_le_rpow_of_height hdeg hx.le hδ hheight hlarge (hinterval t ht)))

end NairTenenbaum
