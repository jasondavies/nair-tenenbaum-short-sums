module

public import NairTenenbaum.PrimeArgumentSieve
public import NairTenenbaum.SieveLevel

@[expose] public section

/-! # Absorbing the prime-argument sieve remainder

The additional logarithm costs an arbitrarily small power in the sieve level.
The threshold is uniform in the constant term of the original polynomial.
-/

namespace NairTenenbaum

open Finset Polynomial

theorem exists_sieveProduct_inv_mul_log_le_rpow (g : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      ∀ z : ℝ, 2 ≤ z → (sieveProduct Q z)⁻¹ * Real.log z ≤ B * z ^ δ := by
  obtain ⟨B, hB, H⟩ := exists_sieveProduct_inv_le_rpow g (by linarith : 0 < δ / 2)
  refine ⟨max 1 (B / (δ / 2)), le_max_left _ _, ?_⟩
  intro Q hQ hdeg z hz
  have hz0 : 0 < z := by linarith
  calc
    _ ≤ (B * z ^ (δ / 2)) * (z ^ (δ / 2) / (δ / 2)) :=
      mul_le_mul (H Q hQ hdeg z hz) (Real.log_le_rpow_div hz0.le (by linarith))
        (Real.log_nonneg (by linarith)) (by positivity)
    _ = (B / (δ / 2)) * z ^ δ := by
      rw [show z ^ δ = z ^ (δ / 2) * z ^ (δ / 2) by
        rw [← Real.rpow_add hz0]; congr 1; ring]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hz0.le _)

noncomputable def primeArgumentConditionalMainTerm {r : ℕ} (Q : ℤ[X]) (g : ℕ)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) (z : ℝ) : ℝ :=
  ((b : ℝ) - a) * sieveProduct Q z * totientTwist 1 (Q.eval 0).natAbs *
    totientTwist (g + 1) (mass m) / Real.log z *
    ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)

theorem exists_primeArgument_conditional_sieve_level_bound (g : ℕ)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K B : ℝ, 1 ≤ K ∧ 1 ≤ B ∧
      ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.eval 0 ≠ 0 → Q.natDegree ≤ g →
      ∀ (r : ℕ) (R : Fin r → ℤ[X]) (m : Tuple r),
      (Pairwise fun i j => Nat.Coprime (m i) (m j)) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      B * (mass m : ℝ) * z ^ (4 * ((g : ℝ) + 1) * (1 + η) + δ) ≤ (b : ℝ) - a →
      (conditionalPolynomialSiftedCount (Q * X)
        (primeArgumentSieveModulus Q g (mass m) z) R m a b : ℝ) ≤
        K * primeArgumentConditionalMainTerm Q g R m a b z := by
  obtain ⟨K, hK, hcount⟩ := exists_primeArgument_conditional_sieve_bound g hη
  obtain ⟨B, hB, hinv⟩ := exists_sieveProduct_inv_mul_log_le_rpow g hδ
  refine ⟨2 * K, B, by linarith, hB, ?_⟩
  intro Q hQ hzero hdeg r R m hpair a b z hab hz hzlog hlevel
  let A : ℝ := 4 * ((g : ℝ) + 1) * (1 + η)
  let D : ℝ := ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)
  have hz0 : 0 < z := by linarith
  have hlog : 0 < Real.log z := by linarith
  have hS := sieveProduct_pos hQ z
  have hD : 0 ≤ D := prod_nonneg (fun _ _ => by positivity)
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hlevel' : (mass m : ℝ) * z ^ A * ((sieveProduct Q z)⁻¹ * Real.log z) ≤
      (b : ℝ) - a := by
    calc
      _ ≤ (mass m : ℝ) * z ^ A * (B * z ^ δ) :=
        mul_le_mul_of_nonneg_left (hinv Q hQ hdeg z hz)
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hz0.le _))
      _ = B * (mass m : ℝ) * z ^ (A + δ) := by rw [Real.rpow_add hz0]; ring
      _ ≤ _ := hlevel
  have hlevel'' : (mass m : ℝ) * z ^ A ≤ ((b : ℝ) - a) * sieveProduct Q z / Real.log z := by
    apply (le_div_iff₀ hlog).mpr
    have H := mul_le_mul_of_nonneg_right hlevel' hS.le
    have heq : (mass m : ℝ) * z ^ A * ((sieveProduct Q z)⁻¹ * Real.log z) *
        sieveProduct Q z = (mass m : ℝ) * z ^ A * Real.log z := by
      field_simp
    rwa [heq] at H
  have herr : (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ A ≤
      primeArgumentConditionalMainTerm Q g R m a b z := by
    have hbase : 0 ≤ D * (((b : ℝ) - a) * sieveProduct Q z / Real.log z) :=
      mul_nonneg hD (div_nonneg (mul_nonneg hL hS.le) hlog.le)
    calc
      _ = D * ((mass m : ℝ) * z ^ A) := by rw [← mass_mul_root_density R m]; dsimp [D]; ring
      _ ≤ D * (((b : ℝ) - a) * sieveProduct Q z / Real.log z) :=
        mul_le_mul_of_nonneg_left hlevel'' hD
      _ ≤ D * (((b : ℝ) - a) * sieveProduct Q z / Real.log z) *
          (totientTwist 1 (Q.eval 0).natAbs * totientTwist (g + 1) (mass m)) :=
        le_mul_of_one_le_right hbase (one_le_mul_of_one_le_of_one_le
          (totientTwist_one_le _ (Int.natAbs_ne_zero.mpr hzero))
          (totientTwist_one_le _ (mass_pos m).ne'))
      _ = _ := by dsimp [primeArgumentConditionalMainTerm, D]; ring
  have H := hcount Q hQ hzero hdeg r R m hpair a b z hab hz hzlog
  calc
    _ ≤ K * (primeArgumentConditionalMainTerm Q g R m a b z +
        (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ A) := H
    _ ≤ K * (primeArgumentConditionalMainTerm Q g R m a b z +
        primeArgumentConditionalMainTerm Q g R m a b z) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl herr) (zero_le_one.trans hK)
    _ = _ := by ring

end NairTenenbaum
