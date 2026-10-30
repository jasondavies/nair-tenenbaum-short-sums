module

public import NairTenenbaum.RootIdealCorrectionGrowth

@[expose] public section

/-! # Summable higher-prime-power tails of the correction

For sufficiently large primes the exponential coefficient bound gives an
`O(p⁻²)` tail. At primes where the linear coefficient vanishes this controls
the whole positive-exponent local correction.
-/

namespace NairTenenbaum

open Polynomial NumberField

variable (K : Type*) [Field K] [NumberField K]

theorem rootIdealCorrection_higherPower_tail {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p : ℕ} (hp : p.Prime) (hlarge : 2 * rootIdealCorrectionGrowthConstant K Q ≤ p) :
    Summable (fun k : ℕ => |rootIdealCorrection K Q (p ^ (k + 2))| / (p : ℝ) ^ (k + 2)) ∧
      (∑' k : ℕ, |rootIdealCorrection K Q (p ^ (k + 2))| / (p : ℝ) ^ (k + 2)) ≤
        2 * rootIdealCorrectionGrowthConstant K Q ^ 2 / (p : ℝ) ^ 2 := by
  let C := rootIdealCorrectionGrowthConstant K Q
  let r : ℝ := C / p
  have hC : 0 < C := rootIdealCorrectionGrowthConstant_pos K Q
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hr0 : 0 ≤ r := (div_pos hC hp0).le
  have hr : r ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by dsimp [C] at *; linarith)
  have hr1 : r < 1 := by linarith
  have hgeom : Summable (fun k : ℕ => r ^ (k + 2)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hr0 hr1).mul_right (r ^ 2)
  have hbound (k : ℕ) :
      |rootIdealCorrection K Q (p ^ (k + 2))| / (p : ℝ) ^ (k + 2) ≤ r ^ (k + 2) := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (rootIdealCorrection_prime_pow_exponential_bound K hQ hp _)
      (pow_nonneg hp0.le _)
  have hsum := hgeom.of_nonneg_of_le (fun k => div_nonneg (abs_nonneg _) (pow_nonneg hp0.le _)) hbound
  refine ⟨hsum, (hsum.tsum_le_tsum hbound hgeom).trans ?_⟩
  have Hsum : (∑' k : ℕ, r ^ (k + 2)) = r ^ 2 * (1 - r)⁻¹ := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, mul_comm]
  rw [Hsum]
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (show 1 / 2 ≤ 1 - r by linarith)
    simpa only [one_div, inv_div, inv_one, mul_one, inv_inv] using H
  calc
    _ ≤ r ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg r)
    _ = 2 * C ^ 2 / (p : ℝ) ^ 2 := by dsimp [r]; ring

theorem rootIdealCorrection_positivePower_tail {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p : ℕ} (hp : p.Prime) (hlarge : 2 * rootIdealCorrectionGrowthConstant K Q ≤ p)
    (hcancel : rootIdealCorrection K Q p = 0) :
    Summable (fun k : ℕ => |rootIdealCorrection K Q (p ^ (k + 1))| / (p : ℝ) ^ (k + 1)) ∧
      (∑' k : ℕ, |rootIdealCorrection K Q (p ^ (k + 1))| / (p : ℝ) ^ (k + 1)) ≤
        2 * rootIdealCorrectionGrowthConstant K Q ^ 2 / (p : ℝ) ^ 2 := by
  obtain ⟨hsum, hbound⟩ := rootIdealCorrection_higherPower_tail K hQ hp hlarge
  have H : Summable (fun k : ℕ => |rootIdealCorrection K Q (p ^ (k + 1))| / (p : ℝ) ^ (k + 1)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.add_assoc] using hsum
  refine ⟨H, ?_⟩
  rw [H.tsum_eq_zero_add]
  simpa only [Nat.zero_add, pow_one, hcancel, abs_zero, zero_div, zero_add, Nat.add_assoc] using hbound

theorem rootIdealCorrection_minpoly_goodPrime_tail_summable (θ : 𝓞 K) :
    Summable (fun p : ℕ =>
      if p.Prime ∧ 2 * rootIdealCorrectionGrowthConstant K (minpoly ℤ θ) ≤ p ∧
          p.Coprime (RingOfIntegers.exponent θ) then
        ∑' k : ℕ, |rootIdealCorrection K (minpoly ℤ θ) (p ^ (k + 1))| / (p : ℝ) ^ (k + 1)
      else 0) := by
  have hQ : (minpoly ℤ θ).IsPrimitive := (minpoly.monic (RingOfIntegers.isIntegral θ)).isPrimitive
  have HM : Summable (fun p : ℕ =>
      2 * rootIdealCorrectionGrowthConstant K (minpoly ℤ θ) ^ 2 / (p : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left
        (2 * rootIdealCorrectionGrowthConstant K (minpoly ℤ θ) ^ 2)
  apply HM.of_nonneg_of_le
  · intro p
    split_ifs
    · exact tsum_nonneg (fun k => div_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg p) _))
    · exact le_rfl
  · intro p
    split_ifs with hp
    · exact (rootIdealCorrection_positivePower_tail K hQ hp.1 hp.2.1
        (rootIdealCorrection_minpoly_prime_eq_zero K θ hp.1 hp.2.2)).2
    · positivity

end NairTenenbaum
