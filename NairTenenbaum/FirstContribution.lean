module

public import NairTenenbaum.SmallDivisorMajorant
public import NairTenenbaum.SmallDivisorMainTerm
public import NairTenenbaum.PolynomialValueBounds

@[expose] public section

/-! # The small-prefix, large-next-prime contribution

This class contains the first class in §4: a prefix of the irreducible value
factorization has small weighted mass, and its next-prime cutoff exceeds the
sieve bound. No choice of a first crossing prime is built into the class, so
its estimate also applies to any such prefix.
-/

namespace NairTenenbaum

/-- A small whole-prime-power prefix with a large cutoff. -/
def PolynomialSystem.HasSmallRoughPrefix {k r : ℕ} (P : PolynomialSystem k r)
    (N : ℕ+) (z : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧
    weightedMass P.exponent (primeSelect n (Finset.range q)) ≤ N ∧ z < (q : ℝ)

noncomputable def PolynomialSystem.smallRoughContribution {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (a b : ℤ) (z : ℝ) : ℝ := by
  classical
  exact ∑ t ∈ (Finset.Ioc a b).filter (P.HasSmallRoughPrefix N z),
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

/-- The first-contribution reduction, with all counting and roughness inputs
proved and only a total-value upper bound remaining as a hypothesis. -/
theorem PolynomialSystem.smallRoughContribution_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (N : ℕ+) (a b : ℤ) {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.smallRoughContribution F N a b (x ^ α) ≤
      A ^ (c / α) * P.smallDivisorSiftedSum F N a b (x ^ α) := by
  classical
  let T := (Finset.Ioc a b).filter (P.HasSmallRoughPrefix N (x ^ α))
  have hex : ∀ t : ℤ, ∃ (n : Tuple r) (q : ℕ), t ∈ T →
      (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧
      weightedMass P.exponent (primeSelect n (Finset.range q)) ≤ N ∧ x ^ α < (q : ℝ) := by
    intro t
    by_cases ht : t ∈ T
    · obtain ⟨n, q, hn⟩ := (Finset.mem_filter.mp ht).2
      exact ⟨n, q, fun _ => hn⟩
    · exact ⟨1, 0, fun h => (ht h).elim⟩
  choose n q hn using hex
  exact P.sum_roughPrefix_le hF hA hB N a b T n q (Finset.filter_subset _ _)
    (fun t ht => (hn t ht).1) hx hα (fun t ht => (hn t ht).2.2)
    (fun t ht => (hn t ht).2.1) (fun t ht => hvalue t (Finset.mem_filter.mp ht).1)

/-- Uniform main-term bound for the first contribution. The height hypothesis
and elementary interval bounds discharge the polynomial-value estimate. -/
theorem exists_smallRoughContribution_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε δ A : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hδ : 0 < δ) (hA : 1 ≤ A) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → ∀ (B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (polynomialHeight P.total : ℝ) ^ δ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε / 2) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, (t.natAbs : ℝ) ≤ 2 * x) →
      P.smallRoughContribution F N a b (x ^ ((g : ℝ) * ε / 2)) ≤
        K * smallDivisorSieveCost B σ g P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, x₁, hK, hx₁, H⟩ := exists_smallDivisorSiftedSum_mainTerm_bound hg hε hsmall
  let C := A ^ (((g : ℝ) + 1 / δ + 1) / ((g : ℝ) * ε / 2))
  have hC : 0 < C := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hA) _
  refine ⟨C * K, max x₁ (max 2 (((g : ℝ) + 1) * 2 ^ g)), mul_pos hC hK,
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro k r P hdeg B σ F hF hB hσ hσsmall x y N a b hx hheight hN hy hab hlength hlength' hinterval
  have hx₂ : 2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hlarge : ((g : ℝ) + 1) * 2 ^ g ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hα : 0 < (g : ℝ) * ε / 2 := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  have H' := P.smallRoughContribution_le hF hA (zero_le_one.trans hB) N a b
    (by linarith : 1 < x) hα (fun t ht => eval_natAbs_le_rpow_of_height hdeg
      (by linarith) hδ hheight hlarge (hinterval t ht))
  have H'' := mul_le_mul_of_nonneg_left
    (H k r P hdeg A B σ F hF (zero_le_one.trans hA) hB hσ hσsmall x y N a b
      ((le_max_left _ _).trans hx) hN hy hab hlength hlength') hC.le
  exact H'.trans (by simpa only [C, mul_assoc] using H'')

end NairTenenbaum
