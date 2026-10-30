module

public import NairTenenbaum.SieveProductLowerBound

@[expose] public section

/-! # Absorbing the conditional sieve remainder at an explicit level -/

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem mass_mul_root_density {r : ℕ} (R : Fin r → ℤ[X]) (m : Tuple r) :
    (mass m : ℝ) * (∏ i, ((rootCount (R i) (m i) : ℝ) / m i)) =
      ∏ i, (rootCount (R i) (m i) : ℝ) := by
  rw [Finset.prod_div_distrib]
  have hmass : (∏ i, (m i : ℝ)) = (mass m : ℝ) := by simp only [mass, Nat.cast_prod]
  rw [hmass]
  exact mul_div_cancel₀ _ (by exact_mod_cast (mass_pos m).ne')

noncomputable def conditionalSieveMainTerm {r : ℕ} (Q : ℤ[X]) (g : ℕ)
    (R : Fin r → ℤ[X]) (m : Tuple r) (a b : ℤ) (z : ℝ) : ℝ :=
  ((b : ℝ) - a) * sieveProduct Q z * totientTwist g (mass m) *
    ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)

/-- Explicit cutoff growth is sufficient to absorb the entire conditional
sieve remainder, uniformly in the conditioning polynomials and moduli. -/
theorem exists_conditional_sieve_level_bound {g : ℕ} (hg : 0 < g)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ K B : ℝ, 1 ≤ K ∧ 1 ≤ B ∧
      ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      ∀ (r : ℕ) (R : Fin r → ℤ[X]) (m : Tuple r),
      (Pairwise fun i j => Nat.Coprime (m i) (m j)) →
      ∀ (a b : ℤ) (z : ℝ), a ≤ b → 2 ≤ z → 16 ≤ Real.log z →
      B * (mass m : ℝ) * z ^ (4 * (g : ℝ) * (1 + η) + δ) ≤ (b : ℝ) - a →
      (conditionalPolynomialSiftedCount Q (sieveModulus Q (mass m) z) R m a b : ℝ) ≤
        K * conditionalSieveMainTerm Q g R m a b z := by
  obtain ⟨K, hK, hcount⟩ := exists_restored_conditional_sieve_bound hg hη
  obtain ⟨B, hB, hinv⟩ := exists_sieveProduct_inv_le_rpow g hδ
  refine ⟨2 * K, B, by linarith, hB, ?_⟩
  intro Q hQ hdeg r R m hpair a b z hab hz hzlog hlevel
  let A : ℝ := 4 * (g : ℝ) * (1 + η)
  let D : ℝ := ∏ i, ((rootCount (R i) (m i) : ℝ) / m i)
  have hz₀ : 0 < z := by linarith
  have hS := sieveProduct_pos hQ z
  have hD : 0 ≤ D := Finset.prod_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hlevel' : (mass m : ℝ) * z ^ A * (sieveProduct Q z)⁻¹ ≤ (b : ℝ) - a := by
    calc
      _ ≤ (mass m : ℝ) * z ^ A * (B * z ^ δ) :=
        mul_le_mul_of_nonneg_left (hinv Q hQ hdeg z hz)
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hz₀.le _))
      _ = B * (mass m : ℝ) * z ^ (A + δ) := by rw [Real.rpow_add hz₀]; ring
      _ ≤ _ := hlevel
  have hlevel'' : (mass m : ℝ) * z ^ A ≤ ((b : ℝ) - a) * sieveProduct Q z := by
    have H := mul_le_mul_of_nonneg_right hlevel' hS.le
    simpa only [mul_assoc, inv_mul_cancel₀ hS.ne', mul_one] using H
  have herr : (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ A ≤ conditionalSieveMainTerm Q g R m a b z := by
    calc
      _ = D * ((mass m : ℝ) * z ^ A) := by rw [← mass_mul_root_density R m]; dsimp [D]; ring
      _ ≤ D * (((b : ℝ) - a) * sieveProduct Q z) := mul_le_mul_of_nonneg_left hlevel'' hD
      _ ≤ D * (((b : ℝ) - a) * sieveProduct Q z) * totientTwist g (mass m) :=
        le_mul_of_one_le_right (mul_nonneg hD (mul_nonneg hL hS.le)) (totientTwist_one_le g (mass_pos m).ne')
      _ = _ := by dsimp [conditionalSieveMainTerm, D]; ring
  have H := hcount Q hQ hdeg r R m hpair a b z hab hz hzlog
  calc
    _ ≤ K * (conditionalSieveMainTerm Q g R m a b z +
        (∏ i, (rootCount (R i) (m i) : ℝ)) * z ^ A) := H
    _ ≤ K * (conditionalSieveMainTerm Q g R m a b z + conditionalSieveMainTerm Q g R m a b z) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl herr) (zero_le_one.trans hK)
    _ = _ := by ring

end NairTenenbaum
