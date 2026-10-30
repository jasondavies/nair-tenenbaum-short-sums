/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import NairTenenbaum.PrimeArguments.PrimeArgumentSmallSum

/-! # Sieve levels for prime arguments with the original degree and growth exponent -/

@[expose] public section

namespace NairTenenbaum

/-- The smaller prime cutoff accommodates the enlarged sieve dimension, even
for prefix masses up to `x^(3g²ε)`. -/
theorem primeArgument_scale_exponent {g : ℕ} (hg : 0 < g) (ε : ℝ) (hε : 0 ≤ ε) :
    3 * (g : ℝ) ^ 2 * ε + (g : ℝ) * ε / 16 *
      (4 * ((g : ℝ) + 1) * (1 + 1 / 16) + 1 / 4) + (g : ℝ) ^ 2 * ε / 4 ≤
        4 * (g : ℝ) ^ 2 * ε := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  nlinarith [mul_nonneg hε (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
    (sub_nonneg.mpr hg₁))]

/-- One uniform threshold makes the chosen cutoffs satisfy the logarithmic
and size conditions of the conditional sieve, including a factor two for passing
to integer endpoints. -/
theorem exists_primeArgument_sieve_scales {g : ℕ} (hg : 0 < g) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL : 1 ≤ L) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      2 ≤ x ^ ((g : ℝ) * ε / 16) ∧ 16 ≤ Real.log (x ^ ((g : ℝ) * ε / 16)) ∧
      ∀ N y : ℝ, 0 ≤ N → N ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) →
        x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
        L * N * (x ^ ((g : ℝ) * ε / 16)) ^
          (4 * ((g : ℝ) + 1) * (1 + 1 / 16) + 1 / 4) ≤ y / 2 := by
  let α : ℝ := (g : ℝ) * ε / 16
  let e : ℝ := (g : ℝ) ^ 2 * ε / 4
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hα : 0 < α := by dsimp [α]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  let t : ℝ := max 0 (max (16 / α) (Real.log (2 * L) / e))
  refine ⟨Real.exp t, Real.one_le_exp_iff.mpr (le_max_left _ _), ?_⟩
  intro x hx
  have hx₁ : 1 ≤ x := (Real.one_le_exp_iff.mpr (le_max_left _ _)).trans hx
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx₁
  have ht : t ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hx
  have hlog : 16 ≤ Real.log (x ^ α) := by
    rw [Real.log_rpow hx₀]
    have H : 16 / α ≤ Real.log x := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
    exact (div_le_iff₀ hα).mp H |>.trans_eq (mul_comm _ _)
  have htwo : 2 ≤ x ^ α := by
    have H := Real.add_one_le_exp (Real.log (x ^ α))
    rw [Real.exp_log (Real.rpow_pos_of_pos hx₀ α)] at H
    linarith
  have hgap : 2 * L ≤ x ^ e := by
    have H : Real.log (2 * L) / e ≤ Real.log x :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ht)
    have H' : Real.log (2 * L) ≤ Real.log (x ^ e) := by
      rw [Real.log_rpow hx₀]
      nlinarith [(div_le_iff₀ he).mp H]
    exact (Real.log_le_log_iff (by linarith : 0 < 2 * L)
      (Real.rpow_pos_of_pos hx₀ e)).mp H'
  refine ⟨htwo, hlog, ?_⟩
  intro N y hN hNx hy
  have hpow := Real.rpow_nonneg hx₀.le (α * (4 * ((g : ℝ) + 1) * (1 + 1 / 16) + 1 / 4))
  have H := mul_le_mul hgap hNx hN (Real.rpow_nonneg hx₀.le e)
  have H' := mul_le_mul_of_nonneg_right H hpow
  rw [← Real.rpow_add hx₀, ← Real.rpow_add hx₀] at H'
  have hexp : e + 3 * (g : ℝ) ^ 2 * ε +
      α * (4 * ((g : ℝ) + 1) * (1 + 1 / 16) + 1 / 4) ≤ 4 * (g : ℝ) ^ 2 * ε := by
    dsimp only [e, α]
    linarith [primeArgument_scale_exponent hg ε hε.le]
  have H'' := H'.trans ((Real.rpow_le_rpow_of_exponent_le hx₁ hexp).trans hy)
  rw [Real.rpow_mul hx₀.le] at H''
  change L * N * (x ^ α) ^ (4 * ((g : ℝ) + 1) * (1 + 1 / 16) + 1 / 4) ≤ y / 2
  nlinarith

/-- The same threshold works throughout all smaller logarithmic bands. -/
theorem exists_primeArgument_variable_sieve_scales {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) {L : ℝ} (hL : 1 ≤ L) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ N y z : ℝ, 0 ≤ N → N ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) →
        x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → 0 ≤ z → z ≤ x ^ ((g : ℝ) * ε / 16) →
        L * N * z ^ (4 * ((g : ℝ) + 1) * (1 + 1 / 16) + 1 / 4) ≤ y / 2 := by
  obtain ⟨x₀, hx₀, H⟩ := exists_primeArgument_sieve_scales hg hε hL
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx N y z hN hNx hy hz hzx
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz hzx (by positivity))
    (mul_nonneg (zero_le_one.trans hL) hN)).trans ((H x hx).2.2 N y hN hNx hy)

/-- The divisor sum at the reduced sieve cutoff, with constants chosen before
all polynomial coefficients and the admissible arithmetic function. -/
theorem exists_primeSmallDivisorSiftedSum_at_scales {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K x₀ : ℝ, 1 ≤ K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → P.total.eval 0 ≠ 0 → ∀ (A B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 0 ≤ A → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a →
      P.primeSmallDivisorSiftedSum F g N a b (x ^ ((g : ℝ) * ε / 16)) ≤
        K * primeArgumentSmallSieveCost B σ g P.badDiscriminant * ((b : ℝ) - a) *
          sieveProduct P.total (x ^ ((g : ℝ) * ε / 16)) *
          (∑ n ∈ Finset.Icc 1 N, P.weight F n) *
            primeArgumentFactor P.total (x ^ ((g : ℝ) * ε / 16)) := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeSmallDivisorSiftedSum_bound hg
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨x₀, hx₀, hx⟩ := exists_primeArgument_sieve_scales hg hε hL
  refine ⟨K, x₀, hK, hx₀, ?_⟩
  intro k r P hdeg hzero A B σ F hF hA hB hσ hsmall x y N a b hxx hN hy hab hlength
  obtain ⟨hz, hzlog, hlevel⟩ := hx x hxx
  exact H k r P hdeg hzero A B σ F hF hA hB hσ hsmall N a b _ hab hz hzlog
    ((hlevel N y (by positivity) hN hy).trans hlength)

end NairTenenbaum
