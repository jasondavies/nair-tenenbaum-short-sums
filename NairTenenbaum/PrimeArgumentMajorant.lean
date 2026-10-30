module

public import NairTenenbaum.SmallDivisorMajorant
public import NairTenenbaum.PrimeArgumentSieve

@[expose] public section

/-! # Prime arguments in the selected-prefix majorant

Primality supplies the extra sieve condition for `X`. The value decomposition
and its growth bound continue to use the original polynomial system.
-/

namespace NairTenenbaum

open Finset Polynomial

noncomputable def PolynomialSystem.primeSmallDivisorSiftedSum {k r : ℕ}
    (P : PolynomialSystem k r) (F : ArithmeticMap k) (g : ℕ) (N : ℕ+)
    (a b : ℤ) (z : ℝ) : ℝ :=
  ∑ v ∈ smallDivisorTuples P.exponent N, pullback P.exponent F v *
    conditionalPolynomialSiftedCount (P.total * X)
      (primeArgumentSieveModulus P.total g (mass v) z) P.R v a b


/-- Grouping a selected divisor for each integer by its tuple gives the sifted
small-divisor majorant. Distinct integers can have the same selected tuple. -/
theorem PolynomialSystem.sum_selectedPrimeDivisors_le {k r : ℕ} (P : PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (g : ℕ) (N : ℕ+) (a b : ℤ) (z : ℝ)
    (T : Finset ℤ) (m : ℤ → Tuple r) (hT : T ⊆ Finset.Ioc a b)
    (hz : 0 ≤ z) (htPrime : ∀ t ∈ T, t.natAbs.Prime)
    (htLarge : ∀ t ∈ T, z < t.natAbs)
    (hm : ∀ t ∈ T, weightedMass P.exponent (m t) ≤ N)
    (hdiv : ∀ t ∈ T, ∀ i, (m t i : ℤ) ∣ (P.R i).eval t)
    (hsift : ∀ t ∈ T, Nat.Coprime (sieveModulus P.total (mass (m t)) z) (P.total.eval t).natAbs) :
    (∑ t ∈ T, pullback P.exponent F (m t)) ≤ P.primeSmallDivisorSiftedSum F g N a b z := by
  classical
  have hmap : ∀ t ∈ T, m t ∈ smallDivisorTuples P.exponent N := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨mem_tupleBox.mpr (fun i =>
      (coordinate_le_weightedMass P.exponent P.exponent_pos (m t) i).trans (hm t ht)), hm t ht⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  unfold PolynomialSystem.primeSmallDivisorSiftedSum
  apply Finset.sum_le_sum
  intro v hv
  have hcard : (T.filter (fun t => m t = v)).card ≤
      conditionalPolynomialSiftedCount (P.total * X) (primeArgumentSieveModulus P.total g (mass v) z) P.R v a b := by
    unfold conditionalPolynomialSiftedCount polynomialCongruenceSet
    apply Finset.card_le_card
    intro t ht
    obtain ⟨ht, hmt⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hT ht, hmt ▸ hdiv t ht⟩,
      primeArgumentSieveModulus_coprime_mul_X P.total g (mass v) hz t
        (htPrime t ht) (htLarge t ht) (hmt ▸ hsift t ht)⟩
  calc
    _ = (T.filter (fun t => m t = v)).card * pullback P.exponent F v := by
      rw [Finset.sum_congr rfl (fun t ht => congrArg (pullback P.exponent F) (Finset.mem_filter.mp ht).2)]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      rw [mul_comm (pullback P.exponent F v)]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hF _)

/-- Equation (31), with explicit growth constant and a proven sieve condition.
The finite set can be any part of the interval whose selected prefixes are small
and whose next-prime cutoffs exceed `x^α`. -/
theorem PolynomialSystem.sum_primeRoughPrefix_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (g : ℕ) (N : ℕ+) (a b : ℤ) (T : Finset ℤ) (n : ℤ → Tuple r) (q : ℤ → ℕ)
    (hT : T ⊆ Finset.Ioc a b) (hn : ∀ t ∈ T, ∀ i, (n t i : ℕ) = ((P.R i).eval t).natAbs)
    {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (htPrime : ∀ t ∈ T, t.natAbs.Prime) (htLarge : ∀ t ∈ T, x ^ α < t.natAbs)
    (hq : ∀ t ∈ T, x ^ α < (q t : ℝ))
    (hsmall : ∀ t ∈ T, weightedMass P.exponent (primeSelect (n t) (Finset.range (q t))) ≤ N)
    (hvalue : ∀ t ∈ T, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    (∑ t ∈ T, extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)) ≤
      A ^ (c / α) * P.primeSmallDivisorSiftedSum F g N a b (x ^ α) := by
  let m := fun t => primeSelect (n t) (Finset.range (q t))
  have H := P.sum_selectedPrimeDivisors_le hF.nonneg g N a b (x ^ α) T m hT
    (Real.rpow_nonneg (by linarith) _) htPrime htLarge hsmall
    (fun t ht i => Int.natCast_dvd.mpr (by
      simpa only [hn t ht i] using primeSelect_coordinate_dvd (n t) (Finset.range (q t)) i))
    (fun t ht => P.primeSelect_sieve_coprime (hn t ht) (Real.rpow_nonneg (by linarith) _) (hq t ht))
  calc
    _ ≤ ∑ t ∈ T, A ^ (c / α) * pullback P.exponent F (m t) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← P.pullback_valueTuple F (hn t ht)]
      exact hF.pullback_primeSplit_le_of_rough hA hB P.exponent P.exponent_pos (n t) (q t)
        hx hα (hq t ht).le (by simpa only [P.weightedMass_valueTuple (hn t ht)] using hvalue t ht)
    _ = A ^ (c / α) * ∑ t ∈ T, pullback P.exponent F (m t) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left H (Real.rpow_nonneg (by linarith) _)

end NairTenenbaum
