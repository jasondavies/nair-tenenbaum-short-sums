module

public import NairTenenbaum.HooleyLogarithmicSaving

@[expose] public section

/-! # A uniform negligible tail for large divisor-window counts -/

namespace NairTenenbaum

open Real Polynomial Filter
open scoped Topology

noncomputable def polynomialDivisorLargeSum (Q : ℤ[X]) (η x y : ℝ) : ℝ :=
  ∑ n ∈ (shortInterval x y).filter
    (fun n : ℕ => (Real.log x) ^ η < (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)),
    (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ)

theorem exists_polynomialDivisorLargeSum_power_saving {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η : ℝ} (hα : 0 < α)
    (hη : Real.log 4 - 1 < η) :
    ∃ δ x₀ C : ℝ, 0 < δ ∧ 1 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
      x₀ < x → x ^ α ≤ y → y ≤ x →
        polynomialDivisorLargeSum Q η x y ≤ C * y * (Real.log x) ^ (-δ) := by
  obtain ⟨ε, hε, he⟩ := exists_hooley_tail_exponent hη
  let e := (2 : ℝ) ^ (1 + ε) - (1 + ε) - 1
  let δ := -(e - ε * η) / 2
  have hδ : 0 < δ := by dsimp [δ, e]; linarith
  let ζ := Real.sqrt (2 * (1 + ε)) + 1
  obtain ⟨x₁, C, hx₁, hC, H⟩ := exists_hooleyPolynomialSum_sharp_bound hQ hirr
    (t := 1 + ε) (by linarith) hα (show Real.sqrt (2 * (1 + ε)) < ζ by dsimp [ζ]; linarith)
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp (eventually_hooleySubexponential_le_log_rpow ζ hδ)
  refine ⟨δ, max x₁ x₂, C, hδ, hx₁.trans_le (le_max_left _ _), hC, fun x y hx hy hyx => ?_⟩
  have hx₁' : x₁ < x := (le_max_left _ _).trans_lt hx
  have hxpos : 0 < x := by linarith [hx₁.trans hx₁']
  have hl : 0 < Real.log x := Real.log_pos (hx₁.trans hx₁')
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos α).trans_le hy
  have hT : 0 < (Real.log x) ^ η := Real.rpow_pos_of_pos hl η
  have HS := hx₂ x ((le_max_right _ _).trans hx.le)
  have HE : ((Real.log x) ^ η) ^ (-ε) *
      (C * (y * (Real.log x) ^ e * (Real.log x) ^ δ)) = C * y * (Real.log x) ^ (-δ) := by
    rw [← Real.rpow_mul hl.le]
    calc
      _ = C * y * (((Real.log x) ^ (η * -ε) * (Real.log x) ^ e) * (Real.log x) ^ δ) := by ring
      _ = C * y * (Real.log x) ^ ((η * -ε + e) + δ) := by rw [← Real.rpow_add hl, ← Real.rpow_add hl]
      _ = _ := by congr 2; dsimp [δ]; ring
  calc
    _ ≤ ((Real.log x) ^ η) ^ (-ε) * hooleyPolynomialSum Q (1 + ε) x y :=
      polynomialDivisorWindow_large_sum_le Q hypos hT hε.le
    _ ≤ ((Real.log x) ^ η) ^ (-ε) * (C * (y * (Real.log x) ^ e * hooleySubexponential ζ x)) :=
      mul_le_mul_of_nonneg_left (H x y hx₁' hy hyx) (Real.rpow_nonneg hT.le _)
    _ ≤ ((Real.log x) ^ η) ^ (-ε) * (C * (y * (Real.log x) ^ e * (Real.log x) ^ δ)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hT.le _)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left HS (by positivity)) hC.le
    _ = _ := HE

theorem exists_polynomialDivisorLargeSum_small {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η c : ℝ} (hα : 0 < α)
    (hη : Real.log 4 - 1 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x →
      polynomialDivisorLargeSum Q η x y ≤ c * y := by
  obtain ⟨δ, x₁, C, hδ, hx₁, _, H⟩ := exists_polynomialDivisorLargeSum_power_saving hQ hirr hα hη
  have HL : Tendsto (fun x : ℝ => C * (Real.log x) ^ (-δ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using ((tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop).const_mul C
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp (HL.eventually (gt_mem_nhds hc))
  refine ⟨max x₁ x₂, hx₁.trans_le (le_max_left _ _), fun x y hx hy hyx => ?_⟩
  have hx₁' : x₁ < x := (le_max_left _ _).trans_lt hx
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith [hx₁.trans hx₁'] : 0 ≤ x) α).trans hy
  apply (H x y hx₁' hy hyx).trans
  have HB := mul_le_mul_of_nonneg_right (hx₂ x ((le_max_right _ _).trans hx.le)).le hy₀
  simpa only [mul_assoc, mul_right_comm C y] using HB

theorem exists_polynomialDivisorWindowSum_le_hits_add_small {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (hirr : Irreducible (Q.map (Int.castRingHom ℚ))) {α η c : ℝ} (hα : 0 < α)
    (hη : Real.log 4 - 1 < η) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x →
      polynomialDivisorWindowSum Q x y ≤ (Real.log x) ^ η * polynomialDivisorHitCount Q x y + c * y := by
  classical
  obtain ⟨x₀, hx₀, H⟩ := exists_polynomialDivisorLargeSum_small hQ hirr hα hη hc
  refine ⟨x₀, hx₀, fun x y hx hy hyx => ?_⟩
  have HS := polynomialDivisorWindow_small_sum_le Q x y
    (Real.rpow_nonneg (Real.log_pos (hx₀.trans hx)).le η)
  have HL := H x y hx hy hyx
  have HE := Finset.sum_filter_add_sum_filter_not (shortInterval x y)
    (fun n : ℕ => (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ) ≤ (Real.log x) ^ η)
    (fun n : ℕ => (dyadicDivisorCount (Q.eval (n : ℤ)).natAbs y : ℝ))
  simp only [not_le] at HE
  change _ + polynomialDivisorLargeSum Q η x y = polynomialDivisorWindowSum Q x y at HE
  linarith

end NairTenenbaum
