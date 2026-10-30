module

public import NairTenenbaum.SplitSmoothTail
public import NairTenenbaum.PrimeArgumentMoment

@[expose] public section

/-! # Prime-argument smooth tails retaining the full bad-prime mass -/

namespace NairTenenbaum

open Finset

noncomputable def primeArgumentSplitTailBound (A B κ : ℝ) (g D : ℕ) : ℝ :=
  badPrimeMomentBound B g D * smoothTailUniformBound A B κ (g + 1) D

theorem primeArgumentSplitTailBound_pos {A B κ : ℝ} (hB : 0 < B) {g D : ℕ} (hg : 0 < g) (hD : 0 < D) :
    0 < primeArgumentSplitTailBound A B κ g D :=
  mul_pos (badPrimeMomentBound_pos hB hg hD) (smoothTailUniformBound_pos A B κ (g + 1) D)

/-- The moments of the bad and good parts multiply. The cutoff on the bad
part may depend on the good tuple. -/
theorem PolynomialSystem.primeArgument_split_smooth_moment_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hg : 0 < P.total.natDegree) (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * (ε + κ / Real.log z) ≤ 1 / 4)
    (hzκ : (4 : ℝ) ^ (((P.total.natDegree : ℝ) + 1) * κ) ≤ z)
    (N : ℕ+) (U : Tuple r → Finset (Tuple r))
    (hbox : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, u i ≤ N)
    (hs : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    (∑ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∑ u ∈ U v, (badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u *
        (rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist (P.total.natDegree + 1) (v i))) *
          (weightedMass P.exponent (u * v) : ℝ) ^ (κ / Real.log z)) ≤
      primeArgumentSplitTailBound A B κ P.total.natDegree P.badDiscriminant *
        ∑ m ∈ positiveUpTo z, P.weight F m := by
  let V := smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N
  let W := fun v => rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist (P.total.natDegree + 1) (v i)
  let β := κ / Real.log z
  have hβ : 0 ≤ β := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have hW (v : Tuple r) : 0 ≤ W v := mul_nonneg (rootTupleWeight_nonneg P.exponent hF.nonneg P.R v)
    (Finset.prod_nonneg (fun i _ => totientTwist_nonneg _ _))
  have Hlocal (v : Tuple r) (hv : v ∈ V) :
      (∑ u ∈ U v, (badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u * W v) *
        (weightedMass P.exponent (u * v) : ℝ) ^ β) ≤
      badPrimeMomentBound B P.total.natDegree P.badDiscriminant * (W v * (weightedMass P.exponent v : ℝ) ^ β) := by
    have H := P.badPrimeTupleKernel_moment_sum_le hA hB hε hβ hg hsmall (U v) N (hbox v hv) (hs v hv)
    have H' := mul_le_mul_of_nonneg_right H (mul_nonneg (hW v) (Real.rpow_nonneg (Nat.cast_nonneg (weightedMass P.exponent v)) β))
    rw [Finset.sum_mul] at H'
    convert H' using 1
    apply Finset.sum_congr rfl
    intro u _
    rw [weightedMass_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have H := Finset.sum_le_sum Hlocal
  rw [← Finset.mul_sum] at H
  have HM := P.primeArgument_smooth_moment_uniform hF hA hB hε hκ hz hzκ hgε N
  have H' := H.trans (mul_le_mul_of_nonneg_left HM
    (badPrimeMomentBound_pos (lt_of_lt_of_le zero_lt_one hB) hg P.badDiscriminant_pos).le)
  simpa only [primeArgumentSplitTailBound, mul_assoc, V, W, β] using H'

/-- The smooth-tail saving is imposed on the original combined prefix mass.
Arbitrarily large bad-prime powers are allowed and accounted for in the constant. -/
theorem PolynomialSystem.primeArgument_split_smooth_tail_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z X : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hX : 0 < X)
    (hg : 0 < P.total.natDegree) (hgε : (P.total.natDegree : ℝ) * ε ≤ 1 / 8)
    (hsmall : (P.total.natDegree : ℝ) ^ 2 * (ε + κ / Real.log z) ≤ 1 / 4)
    (hzκ : (4 : ℝ) ^ (((P.total.natDegree : ℝ) + 1) * κ) ≤ z)
    (N : ℕ+) (U : Tuple r → Finset (Tuple r))
    (hbox : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, u i ≤ N)
    (hs : ∀ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∀ u ∈ U v, ∀ i, (u i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    (∑ v ∈ smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N,
      ∑ u ∈ (U v).filter (fun u => X < (weightedMass P.exponent (u * v) : ℝ)),
        badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u *
          (rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist (P.total.natDegree + 1) (v i))) ≤
      primeArgumentSplitTailBound A B κ P.total.natDegree P.badDiscriminant *
        Real.exp (-κ * Real.log X / Real.log z) * ∑ m ∈ positiveUpTo z, P.weight F m := by
  classical
  let V := smoothWeightUpTo P.exponent P.discriminant (Finset.Icc 0 ⌊z⌋₊) N
  let W := fun v => rootTupleWeight P.exponent F P.R v * ∏ i, totientTwist (P.total.natDegree + 1) (v i)
  let β := κ / Real.log z
  have hβ : 0 ≤ β := div_nonneg hκ (Real.log_pos (by linarith : 1 < z)).le
  have hlocal (v : Tuple r) (_hv : v ∈ V) := sum_tail_le_moment (U v)
    (fun u => badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical u * W v)
    (fun u => (weightedMass P.exponent (u * v) : ℝ))
    (fun u => mul_nonneg (badPrimeTupleKernel_nonneg hA (zero_le_one.trans hB) _ _ u)
      (mul_nonneg (rootTupleWeight_nonneg P.exponent hF.nonneg P.R v)
        (Finset.prod_nonneg (fun i _ => totientTwist_nonneg _ _))))
    (fun _ => Nat.cast_nonneg _) hX hβ
  have H := Finset.sum_le_sum hlocal
  rw [← Finset.mul_sum] at H
  have HM := P.primeArgument_split_smooth_moment_le hF hA hB hε hκ hz hg hgε hsmall hzκ N U hbox hs
  have H' := H.trans (mul_le_mul_of_nonneg_left HM (Real.rpow_nonneg hX.le (-β)))
  have heq : X ^ (-β) = Real.exp (-κ * Real.log X / Real.log z) := by
    rw [Real.rpow_def_of_pos hX]
    dsimp [β]
    congr 1
    ring
  rw [heq] at H'
  simpa only [V, W, mul_assoc, mul_left_comm] using H'

/-- The same logarithmic threshold controls the extra totient power without
strengthening the admissibility exponent. -/
theorem primeArgument_split_moment_conditions {g : ℕ} (hg : 0 < g) {ε κ z : ℝ}
    (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hlog : 8 * (g : ℝ) ^ 2 * κ ≤ Real.log z) :
    (g : ℝ) * ε ≤ 1 / 8 ∧ (g : ℝ) ^ 2 * (ε + κ / Real.log z) ≤ 1 / 4 ∧
      (4 : ℝ) ^ (((g : ℝ) + 1) * κ) ≤ z := by
  obtain ⟨hgood, hbad, _⟩ := split_moment_conditions hg hε hκ hz hsmall hlog
  refine ⟨hgood, hbad, ?_⟩
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hg₀ : (0 : ℝ) ≤ g := by positivity
  have hlog4 : Real.log 4 ≤ 3 := by
    have H := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have H : ((g : ℝ) + 1) * κ * Real.log 4 ≤ Real.log z := by
    have H₁ := mul_le_mul_of_nonneg_left hlog4 (mul_nonneg (by linarith : (0 : ℝ) ≤ g + 1) hκ)
    have H₂ := mul_nonneg hκ (mul_nonneg hg₀ (sub_nonneg.mpr hg₁))
    have H₃ := mul_nonneg hκ (sub_nonneg.mpr hg₁)
    nlinarith
  have H' := Real.exp_le_exp.mpr H
  rw [Real.exp_log (by linarith : 0 < z)] at H'
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), mul_comm] using H'

end NairTenenbaum
