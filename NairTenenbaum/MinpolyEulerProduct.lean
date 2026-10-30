module

public import NairTenenbaum.NumberFieldResidueRoots
public import NairTenenbaum.IdealNormDirichlet
public import NairTenenbaum.PolynomialSieve

@[expose] public section

/-! # The good-prime root Euler product is bounded by Dedekind zeta

The coefficient comparison uses actual ideals constructed from residue
roots. Distinct prime sets give distinct squarefree moduli, so the finite
Euler expansion is a subsum of the convergent ideal-norm series.
-/

namespace NairTenenbaum

open Finset Real Polynomial NumberField

theorem prime_finset_product_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [prod_insert hp, Nat.squarefree_mul_iff]
    refine ⟨Nat.coprime_prod_right_iff.mpr (fun r hr => ?_),
      (hS p (mem_insert_self _ _)).squarefree, ih (fun r hr => hS r (mem_insert_of_mem hr))⟩
    exact (Nat.coprime_primes (hS p (mem_insert_self _ _)) (hS r (mem_insert_of_mem hr))).mpr
      (by intro h; exact hp (h ▸ hr))

theorem rootCount_prime_finset_product (Q : ℤ[X]) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    rootCount Q (∏ p ∈ S, p) = ∏ p ∈ S, rootCount Q p := by
  rw [rootCount_squarefree (prime_finset_product_squarefree S hS), Nat.primeFactors_prod hS]

theorem rootCount_le_degree_of_monic {Q : ℤ[X]} (hQ : Q.Monic)
    {p : ℕ} (hp : p.Prime) : rootCount Q p ≤ Q.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rootCount_eq_card_filter Q p]
  apply le_trans (Polynomial.card_le_degree_of_subset_roots (p := Q.map (Int.castRingHom (ZMod p))) ?_)
    Polynomial.natDegree_map_le
  intro a ha
  exact (Polynomial.mem_roots (hQ.map _).ne_zero).mpr (by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using (mem_filter.mp ha).2)

variable {K : Type*} [Field K] [NumberField K]

theorem minpoly_goodPrimeProduct_le_idealNormDirichlet (θ : 𝓞 K)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hgood : ∀ p ∈ S, ¬p ∣ RingOfIntegers.exponent θ) {σ : ℝ} (hσ : 1 < σ) :
    (∏ p ∈ S, (1 + (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ))) ≤
      idealNormDirichlet K σ := by
  classical
  have hT (T : Finset ℕ) (hT : T ∈ S.powerset) : ∀ p ∈ T, p.Prime :=
    fun p hp => hS p (mem_powerset.mp hT hp)
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (↑S.powerset : Set (Finset ℕ)) := by
    intro T hTS U hUS hTU
    have H := congrArg Nat.primeFactors hTU
    simpa only [Nat.primeFactors_prod (hT T hTS), Nat.primeFactors_prod (hT U hUS)] using H
  have htotal := (summable_idealNormDirichlet K hσ).sum_le_tsum
    (S.powerset.image (fun T => ∏ p ∈ T, p)) (fun n _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  rw [sum_image hinj] at htotal
  rw [prod_one_add]
  apply le_trans _ htotal
  apply sum_le_sum
  intro T hTS
  rw [prod_mul_distrib, ← Nat.cast_prod, ← rootCount_prime_finset_product _ T (hT T hTS),
    Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _) (-σ), ← Nat.cast_prod]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast rootCount_minpoly_le_card_ideals_norm θ
    (Nat.coprime_prod_left_iff.mpr (fun p hp =>
      (hT T hTS p hp).coprime_iff_not_dvd.mpr (hgood p (mem_powerset.mp hTS hp))))

end NairTenenbaum
