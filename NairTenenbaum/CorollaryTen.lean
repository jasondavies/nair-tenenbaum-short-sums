module

public import NairTenenbaum.GoldbachScales

@[expose] public section

/-! # Corollary 10: Goldbach representations with one prime in a short interval -/

namespace NairTenenbaum

theorem mem_goldbachPrimes_iff (N p : ℕ) (x y : ℝ) :
    p ∈ goldbachPrimes N x y ↔ p ∈ shortInterval x y ∧ p.Prime ∧
      ∃ q : ℕ, q.Prime ∧ p + q = N := by
  rw [goldbachPrimes, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hprime, hqprime⟩
    refine ⟨hp, hprime, N - p, hqprime, ?_⟩
    have := hqprime.pos
    omega
  · rintro ⟨hp, hprime, q, hqprime, hsum⟩
    refine ⟨hp, hprime, ?_⟩
    have hq : N - p = q := by omega
    simpa only [hq] using hqprime

/-- Corollary 10, with the implicit constant quantified before `N,x,y`.
`goldbachCount` counts each choice of the first prime, as in the paper's sum. -/
def CorollaryTen : Prop :=
  ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 < N → ∀ (x y : ℝ),
      (N : ℝ) ^ δ < x → x ^ ε ≤ y → y ≤ x →
      (goldbachCount N x y : ℝ) ≤ C * (((N : ℝ) / N.totient) * y / (Real.log N) ^ 2)

theorem corollaryTen : CorollaryTen := by
  intro ε δ hε _ hδ _
  obtain ⟨C, hC, H⟩ := exists_goldbach_power_length_bound (mul_pos hδ hε)
  refine ⟨C, hC, ?_⟩
  intro N hN x y hx hy hyx
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx₀ : 0 ≤ x := (Real.rpow_nonneg hN₀.le δ).trans hx.le
  have hlength : (N : ℝ) ^ (δ * ε) ≤ y := by
    rw [Real.rpow_mul hN₀.le]
    exact (Real.rpow_le_rpow (Real.rpow_nonneg hN₀.le δ) hx.le hε.le).trans hy
  exact H N hN x y hx₀ hlength hyx

end NairTenenbaum
