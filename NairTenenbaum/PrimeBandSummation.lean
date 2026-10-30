module

public import NairTenenbaum.PrimeBandContribution

@[expose] public section

/-! # Summing the large-prefix logarithmic bands -/

namespace NairTenenbaum

/-- The sum of the original weighted contributions over any finite collection
of eligible bands is bounded uniformly in the number of bands. -/
theorem exists_primeBandSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → ∀ (A B σ κ c : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ A → 1 ≤ B → 0 < σ → 0 ≤ κ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 1 ≤ κ * (3 * (g : ℝ) ^ 2 * ε / 2) / 2 →
      ∀ (x y u : ℝ) (N : ℕ+) (a b : ℤ) (J : Finset ℕ), x₀ ≤ x → 1 < x → 1 ≤ Real.log x →
      0 < u → u ≤ 1 → u ≤ (g : ℝ) * ε / 16 →
      (∀ j ∈ J, 2 ≤ x ^ (u / 2 ^ (j + 1)) ∧ 2 * (g : ℝ) ≤ x ^ (u / 2 ^ (j + 1)) ∧
        16 ≤ Real.log (x ^ (u / 2 ^ (j + 1))) ∧
        8 * (g : ℝ) ^ 2 * κ ≤ Real.log (x ^ (2 * (u / 2 ^ (j + 1))))) →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      (∑ j ∈ J, P.smoothTailPrefixContribution F N (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ (u / 2 ^ (j + 1)))) ≤
        K * smoothTailSieveCost A B κ g P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, x₀, hK, hx₀, H⟩ := exists_primeBandContribution_mainTerm_bound hg hε
  have hden : 0 < 1 - Real.exp (-1) := sub_pos.mpr (by
    rw [Real.exp_lt_one_iff]
    norm_num)
  refine ⟨K * (1 - Real.exp (-1))⁻¹, x₀, mul_pos hK (inv_pos.mpr hden), hx₀, ?_⟩
  intro k r P hdeg A B σ κ c F hF hA hB hσ hκ hσsmall hdecay
    x y u N a b J hxx hx hlog hu hu₁ hucut hJ hN hy hab hlen hlen' hvalue
  have hband (j : ℕ) (hj : j ∈ J) :
      P.smoothTailPrefixContribution F N (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ (u / 2 ^ (j + 1))) ≤
      K * smoothTailSieveCost A B κ g P.badDiscriminant *
        Real.exp (-1 / (u / 2 ^ (j + 1))) * mainTerm P F x y := by
    have hα : 0 < u / 2 ^ (j + 1) := by positivity
    have hαu := dyadic_primeBand_exponent_le hu.le j
    obtain ⟨hz, hgz, hzlog, hwlog⟩ := hJ j hj
    exact H k r P hdeg A B σ κ c F hF hA hB hσ hκ hσsmall hdecay
      x y (u / 2 ^ (j + 1)) N a b hxx hx hlog hα (hαu.trans hu₁)
      ((by linarith : u / 2 ^ (j + 1) ≤ u).trans hucut)
      hz hgz hzlog hwlog hN hy hab hlen hlen' hvalue
  have hcost := (smoothTailSieveCost_pos (A := A) (κ := κ)
    (lt_of_lt_of_le zero_lt_one hB) hg P.badDiscriminant_pos).le
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) _).trans hy
  have hm : 0 ≤ mainTerm P F x y := by
    dsimp only [mainTerm]
    exact mul_nonneg (mul_nonneg hy₀ (sieveProduct_pos P.noFixedPrime x).le)
      (Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n))
  have Hsum := mul_le_mul_of_nonneg_left (sum_dyadic_primeBand_decay_le hu hu₁ J)
    (mul_nonneg (mul_nonneg hK.le hcost) hm)
  apply (Finset.sum_le_sum hband).trans
  calc
    _ = (K * smoothTailSieveCost A B κ g P.badDiscriminant * mainTerm P F x y) *
        ∑ j ∈ J, Real.exp (-1 / (u / 2 ^ (j + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := by convert Hsum using 1; ring

end NairTenenbaum
