module

public import NairTenenbaum.HooleyPrimeMixedBound
public import NairTenenbaum.RootCount

@[expose] public section

/-! # The root-weighted prime step for the Hooley mean

This is the finite form of equation (2.10) in Tenenbaum's weighted mean
argument. Its mixed-term constant is explicit. The main weighted prime sum
is retained; estimating it sharply is a separate prime-ideal-theorem input.
-/

namespace NairTenenbaum

open Finset Real Polynomial

noncomputable def rootPrimeLogWeight (Q : ℤ[X]) (σ : ℝ) (p : ℕ) : ℝ :=
  (rootCount Q p : ℝ) * Real.log p / (p : ℝ) ^ σ

theorem rootPrimeLogWeight_nonneg (Q : ℤ[X]) (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    0 ≤ rootPrimeLogWeight Q σ p :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_le)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem rootPrimeLogWeight_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : p.Prime) :
    rootPrimeLogWeight Q σ p ≤ (Q.natDegree : ℝ) * (Real.log p / p) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpσ : (p : ℝ) ≤ (p : ℝ) ^ σ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp₁ hσ
  unfold rootPrimeLogWeight
  calc
    _ ≤ (Q.natDegree : ℝ) * Real.log p / (p : ℝ) ^ σ :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast rootCount_le_degree hQ hp)
          (Real.log_nonneg hp₁)) (Real.rpow_nonneg hp₀.le _)
    _ ≤ (Q.natDegree : ℝ) * Real.log p / p :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hp₁)) hp₀ hpσ
    _ = _ := by ring

theorem root_weighted_hooleyCrossMoment_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) {q : ℕ} (hq : 1 < q)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ S, rootPrimeLogWeight Q σ p * hooleyPrimeCrossMoment q n p) ≤
      (Q.natDegree : ℝ) * ((Real.log 4 * Real.exp 2) * (4 : ℝ) ^ q *
        ((n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
          hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1)))) := by
  calc
    _ ≤ ∑ p ∈ S, ((Q.natDegree : ℝ) * (Real.log p / p)) * hooleyPrimeCrossMoment q n p :=
      sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (rootPrimeLogWeight_le hQ hσ (hS p hp))
        (hooleyPrimeCrossMoment_nonneg q n p)
    _ = (Q.natDegree : ℝ) * ∑ p ∈ S, (Real.log p / p) * hooleyPrimeCrossMoment q n p := by
      rw [mul_sum]
      simp only [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_sum_hooleyPrimeCrossMoment_le S hS n hq) (Nat.cast_nonneg _)

/-- The exact prime recurrence plus the proved mixed-term estimate. The
coprimality restriction is removed only from nonnegative upper bounds. -/
theorem root_weighted_hooleyMoment_prime_step {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) {q : ℕ} (hq : 1 < q)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ p ∈ S.filter (fun p => ¬p ∣ n), rootPrimeLogWeight Q σ p * hooleyMoment q (p * n)) ≤
      2 * hooleyMoment q n * (∑ p ∈ S, rootPrimeLogWeight Q σ p) +
      (Q.natDegree : ℝ) * ((Real.log 4 * Real.exp 2) * (4 : ℝ) ^ q *
        ((n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
          hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1)))) := by
  let T := S.filter (fun p => ¬p ∣ n)
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime := hS p (mem_filter.mp hp).1
  have Heq : (∑ p ∈ T, rootPrimeLogWeight Q σ p * hooleyMoment q (p * n)) =
      2 * hooleyMoment q n * (∑ p ∈ T, rootPrimeLogWeight Q σ p) +
      ∑ p ∈ T, rootPrimeLogWeight Q σ p * hooleyPrimeCrossMoment q n p := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    rw [hooleyMoment_prime_mul (hT p hp) (mem_filter.mp hp).2 (by omega : 0 < q)]
    ring
  rw [show S.filter (fun p => ¬p ∣ n) = T from rfl, Heq]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (hooleyMoment_nonneg q n))
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro p hp _
    exact rootPrimeLogWeight_nonneg Q σ (hS p hp)
  · exact root_weighted_hooleyCrossMoment_le hQ T hT n hq hσ

end NairTenenbaum
