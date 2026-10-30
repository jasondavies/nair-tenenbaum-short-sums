module

public import NairTenenbaum.Arithmetic

@[expose] public section

/-! # Signs and compact angular coordinates in the mixed embedding space -/

namespace NairTenenbaum

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

variable {K : Type*} [Field K]

noncomputable def mixedPolarCoordinates
    (σ : {w : InfinitePlace K // IsReal w} → Bool) (r : realSpace K)
    (a : {w : InfinitePlace K // IsComplex w} → ℝ) : mixedSpace K :=
  (fun w => if σ w then r w else -r w,
   fun w => (r w : ℂ) * Complex.exp (((2 * a w - 1) * Real.pi : ℝ) * Complex.I))

theorem normAtAllPlaces_mixedPolarCoordinates
    (σ : {w : InfinitePlace K // IsReal w} → Bool) {r : realSpace K}
    (hr : ∀ w, 0 ≤ r w) (a : {w : InfinitePlace K // IsComplex w} → ℝ) :
    normAtAllPlaces (mixedPolarCoordinates σ r a) = r := by
  ext w
  rw [normAtAllPlaces_apply]
  by_cases hw : IsReal w
  · rw [normAtPlace_apply_of_isReal hw]
    change ‖if σ ⟨w, hw⟩ then r w else -r w‖ = r w
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hr w)]
  · have hwc := not_isReal_iff_isComplex.mp hw
    rw [normAtPlace_apply_of_isComplex hwc]
    change ‖(r w : ℂ) * Complex.exp (((2 * a ⟨w, hwc⟩ - 1) * Real.pi : ℝ) * Complex.I)‖ = r w
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hr w)]

theorem exists_mixedPolarCoordinates (x : mixedSpace K) :
    ∃ σ : {w : InfinitePlace K // IsReal w} → Bool,
      ∃ a : {w : InfinitePlace K // IsComplex w} → ℝ,
        a ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) ∧
        mixedPolarCoordinates σ (normAtAllPlaces x) a = x := by
  classical
  let σ : {w : InfinitePlace K // IsReal w} → Bool := fun w => decide (0 ≤ x.1 w)
  let a : {w : InfinitePlace K // IsComplex w} → ℝ :=
    fun w => (Complex.arg (x.2 w) / Real.pi + 1) / 2
  have ha : a ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
    constructor <;> intro w
    · have H : -1 ≤ Complex.arg (x.2 w) / Real.pi :=
        (le_div_iff₀ Real.pi_pos).mpr (by linarith [Complex.neg_pi_lt_arg (x.2 w)])
      dsimp [a]
      linarith
    · have H : Complex.arg (x.2 w) / Real.pi ≤ 1 :=
        (div_le_iff₀ Real.pi_pos).mpr (by linarith [Complex.arg_le_pi (x.2 w)])
      dsimp [a]
      linarith
  refine ⟨σ, a, ha, ?_⟩
  apply Prod.ext
  · ext w
    change (if σ w then normAtAllPlaces x w else -normAtAllPlaces x w) = x.1 w
    rw [normAtAllPlaces_apply, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
    by_cases hw : 0 ≤ x.1 w
    · simp [σ, hw, abs_of_nonneg hw]
    · simp [σ, hw, abs_of_neg (lt_of_not_ge hw)]
  · ext w
    change (normAtAllPlaces x w : ℂ) *
      Complex.exp (((2 * a w - 1) * Real.pi : ℝ) * Complex.I) = x.2 w
    rw [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex w.2]
    have HE : (2 * a w - 1) * Real.pi = Complex.arg (x.2 w) := by
      dsimp [a]
      field_simp
      ring
    rw [HE]
    exact Complex.norm_mul_exp_arg_mul_I (x.2 w)

end NairTenenbaum
