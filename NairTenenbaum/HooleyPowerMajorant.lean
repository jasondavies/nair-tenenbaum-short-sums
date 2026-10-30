module

public import NairTenenbaum.IrreduciblePrimeLogBound
public import NairTenenbaum.PrimeDirichletPoleBound
public import NairTenenbaum.HooleyExponentGap

@[expose] public section

/-! # An explicit power majorant for irreducible polynomial moments

The proved prime-root logarithmic bound turns the differential majorant
into a pure power of `σ−1`. The constants are uniform in the moment order.
-/

namespace NairTenenbaum

open Real Polynomial

noncomputable def hooleyPoleCoefficient (Q : ℤ[X]) (t : ℝ) (q : ℕ) (C : ℝ) : ℝ :=
  (hooleyPrimeErrorConstant Q q ^ (t / q) / ((q : ℝ) - 1)) *
    (2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) ^ (1 - t / q) *
    Real.exp (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) * C)

theorem hooleyPoleCoefficient_nonneg (Q : ℤ[X]) (t C : ℝ) {q : ℕ} (hq : 2 < q) :
    0 ≤ hooleyPoleCoefficient Q t q C := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  unfold hooleyPoleCoefficient
  exact mul_nonneg (mul_nonneg
    (div_nonneg (Real.rpow_nonneg (hooleyPrimeErrorConstant_nonneg Q q) _) (by linarith))
    (Real.rpow_nonneg (by positivity) _)) (Real.exp_nonneg _)

theorem exp_mul_le_of_log_pole {R C δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hR : R ≤ C - Real.log δ) :
    Real.exp (κ * R) ≤ Real.exp (κ * C) * δ ^ (-κ) := by
  apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hR hκ)).trans_eq
  rw [mul_sub, Real.exp_sub, Real.rpow_def_of_pos hδ]
  rw [show Real.log δ * -κ = -(κ * Real.log δ) by ring, Real.exp_neg, div_eq_mul_inv]

theorem hooleyReducedMomentMajorant_le_power {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t σ C : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 2 < q) (htq : t ≤ q)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hR : rootPrimePowerSum Q σ ≤ C - Real.log (σ - 1)) :
    hooleyReducedMomentMajorant Q t q σ ≤
      hooleyPoleCoefficient Q t q C * (σ - 1) ^ (-1 - hooleyMomentExponentGap t q) := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hκ : 0 ≤ ((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) := by
    apply div_nonneg _ (by linarith)
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_self ht (by linarith)))
  have H := exp_mul_le_of_log_pole (by linarith : 0 < σ - 1) hκ hR
  apply (hooleyReducedMomentMajorant_le_pole hQ hq htq hσ hσ₂).trans
  calc
    _ ≤ (hooleyPrimeErrorConstant Q q ^ (t / q) / ((q : ℝ) - 1)) *
        (2 * (Q.natDegree : ℝ) * (Real.log 4 * Real.exp 2)) ^ (1 - t / q) *
        (σ - 1) ^ (t / q - 1) *
        (Real.exp (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) * C) *
          (σ - 1) ^ (-(((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1)))) := by
      apply mul_le_mul_of_nonneg_left H
      exact mul_nonneg (mul_nonneg
        (div_nonneg (Real.rpow_nonneg (hooleyPrimeErrorConstant_nonneg Q q) _) (by linarith))
        (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by linarith) _)
    _ = _ := by
      unfold hooleyPoleCoefficient hooleyMomentExponentGap
      rw [show -1 - (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) - t / q) =
          (t / q - 1) + -(((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1)) by ring,
        Real.rpow_add (by linarith : 0 < σ - 1)]
      ring

theorem exists_irreducible_hooley_power_majorant {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ C b : ℝ, 0 ≤ C ∧ 1 < b ∧ b ≤ 2 ∧ ∀ t : ℝ, 0 ≤ t →
      ∀ q : ℕ, 2 < q → t ≤ q → ∀ σ : ℝ, 1 < σ → σ ≤ b →
        hooleyReducedMomentMajorant Q t q σ ≤
          hooleyPoleCoefficient Q t q C * (σ - 1) ^ (-1 - hooleyMomentExponentGap t q) := by
  obtain ⟨C, b, hC, hb, hbound⟩ := exists_irreducible_rootPrimePowerSum_log_bound hirr
  refine ⟨C, min 2 ((b + 1) / 2), hC, lt_min (by norm_num) (by linarith),
    min_le_left _ _, fun t ht q hq htq σ hσ hσb => ?_⟩
  exact hooleyReducedMomentMajorant_le_power hQ ht hq htq hσ
    (hσb.trans (min_le_left _ _))
    (hbound σ hσ (lt_of_le_of_lt (hσb.trans (min_le_right _ _)) (by linarith))).2

end NairTenenbaum
