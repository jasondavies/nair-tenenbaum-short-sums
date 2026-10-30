module

public import NairTenenbaum.PrimeArgumentIntervalBound
public import NairTenenbaum.PrimeArgumentHeight
public import NairTenenbaum.PrimeShortSum

@[expose] public section

/-! # Theorem 3: short sums at prime arguments

The proof keeps the original polynomial family in the value decomposition
and sieves its product with `X` only at admissible primes. The constants have
the same degree, growth-parameter, and restricted-discriminant uniformity as
in Theorem 1; the constant-term correction remains explicit in the main term.
-/

namespace NairTenenbaum

theorem exists_primeShortSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g → P.total.eval 0 ≠ 0 →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      primeShortSum P.Q F x y ≤ C P.badDiscriminant * primeMainTerm P F x y := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hσ : 0 < ε * δ / 3 := by positivity
  have hσsmall : (g : ℝ) ^ 2 * (ε * δ / 3) ≤ 1 / 8 := by
    have H : ε * δ / 3 ≤ ε := by nlinarith
    exact (mul_le_mul_of_nonneg_left H (sq_nonneg _)).trans hsmall
  let c : ℝ := (g : ℝ) + 1 / δ + 1 / 8
  obtain ⟨x₀, hx₀, C, hC, H⟩ := exists_primeIntegerSum_mainTerm_bound hg hA hB hε hsmall
    hσ hσsmall (show 0 ≤ c by dsimp [c]; positivity)
    (primeArgument_growth_margin hg hε.le hδ hδ₁)
  let τ : ℝ := 4 * (g : ℝ) ^ 2 * ε
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let c₀ := max x₀ (max 2 (max ((((g : ℝ) + 1) * 2 ^ g) ^ (8 : ℕ))
    ((2 : ℝ) ^ (1 / τ))))
  have hc₁ : x₀ ≤ c₀ := le_max_left _ _
  have hc₂ : 2 ≤ c₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hcH : (((g : ℝ) + 1) * 2 ^ g) ^ (8 : ℕ) ≤ c₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcτ : (2 : ℝ) ^ (1 / τ) ≤ c₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨c₀, by linarith, C, hC, ?_⟩
  intro k r P hdeg hzero F hF x y hx hy hyx
  have hH : (1 : ℝ) ≤ (polynomialHeight P.total : ℝ) := by
    exact_mod_cast polynomialHeight_pos P.total_ne_zero
  have hHδ : 1 ≤ (polynomialHeight P.total : ℝ) ^ δ := Real.one_le_rpow hH hδ.le
  have hcx : c₀ ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ c₀) hHδ).trans hx.le
  have hx₂ : 2 ≤ x := hc₂.trans hcx
  have hx₁ : 1 ≤ x := by linarith
  have hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x :=
    (le_mul_of_one_le_left (zero_le_one.trans hHδ) (by linarith : 1 ≤ c₀)).trans hx.le
  have hy₂ : 2 ≤ y := by
    have Hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (hcτ.trans hcx) hτ.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hτ.ne',
      Real.rpow_one] at Hpow
    exact Hpow.trans hy
  obtain ⟨hab, hlen, hlen', hvalues⟩ := shortInterval_endpoint_bounds (by linarith : 0 ≤ x) hy₂ hyx
  rw [P.primeShortSum_eq_primeIntegerSum F (by linarith : 0 ≤ x) y]
  apply H k r P hdeg hzero F hF x y _ _ (hc₁.trans hcx) hy hab
    (by simpa only [Int.cast_natCast] using hlen) (by simpa only [Int.cast_natCast] using hlen')
  intro t ht
  exact eval_natAbs_le_primeArgument_rpow hdeg hx₁ hδ hheight (hcH.trans hcx) (hvalues t ht)

/-- Theorem 3, with a coefficient-independent height threshold and the
restricted-discriminant dependence displayed in the order of quantifiers. -/
def TheoremThree : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (P : PolynomialSystem k r), P.total.natDegree = g → P.total.eval 0 ≠ 0 →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
          ∀ x y : ℝ, c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
            x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
            primeShortSum P.Q F x y ≤ C P.badDiscriminant * primeMainTerm P F x y

theorem theoremThree : TheoremThree := by
  intro k r g _ _ hg A B ε δ hA hB hε hsmall hδ hδ₁
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hsmall' : (g : ℝ) ^ 2 * ε ≤ 1 / 8 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * (g : ℝ) ^ 2)).mp hsmall
    nlinarith
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_primeShortSum_mainTerm_bound hg hA hB hε hsmall' hδ hδ₁
  exact ⟨c₀, hc₀, C, hC, H k r⟩

end NairTenenbaum
