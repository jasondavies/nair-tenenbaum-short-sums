module

public import NairTenenbaum.PrimeThreshold
public import NairTenenbaum.RoughCofactorBounds

@[expose] public section

/-! # Smooth and rough parts at a real cutoff -/

namespace NairTenenbaum

noncomputable def smoothPart (n : ℕ+) (z : ℝ) : ℕ+ :=
  primeSelect (fun _ : Fin 1 => n) (Finset.range (⌊z⌋₊ + 1)) 0

noncomputable def roughPart (n : ℕ+) (z : ℝ) : ℕ+ :=
  primeReject (fun _ : Fin 1 => n) (Finset.range (⌊z⌋₊ + 1)) 0

theorem smoothPart_mul_roughPart (n : ℕ+) (z : ℝ) : smoothPart n z * roughPart n z = n := by
  exact congrFun (primeSelect_mul_primeReject (fun _ : Fin 1 => n) (Finset.range (⌊z⌋₊ + 1))) 0

theorem smoothPart_roughPart_coprime (n : ℕ+) (z : ℝ) :
    Nat.Coprime (smoothPart n z) (roughPart n z) :=
  primeSelect_primeReject_coprime (fun _ : Fin 1 => n) (Finset.range (⌊z⌋₊ + 1)) 0 0

theorem prime_le_of_mem_smoothPart (n : ℕ+) {z : ℝ} (hz : 0 ≤ z) {p : ℕ}
    (hp : p ∈ (smoothPart n z : ℕ).primeFactors) : (p : ℝ) ≤ z := by
  have H := primeSelect_range_prime_lt (fun _ : Fin 1 => n) (⌊z⌋₊ + 1) 0 hp
  exact (by exact_mod_cast (show p ≤ ⌊z⌋₊ by omega) : (p : ℝ) ≤ ⌊z⌋₊).trans (Nat.floor_le hz)

theorem cutoff_lt_of_mem_roughPart (n : ℕ+) (z : ℝ) {p : ℕ}
    (hp : p ∈ (roughPart n z : ℕ).primeFactors) : z < (p : ℝ) := by
  have H := primeReject_range_prime_ge (fun _ : Fin 1 => n) (⌊z⌋₊ + 1) 0 hp
  exact Nat.lt_of_floor_lt (by omega)

theorem log_roughPart (n : ℕ+) (z : ℝ) :
    Real.log (roughPart n z : ℕ) = Real.log (n : ℕ) - Real.log (smoothPart n z : ℕ) := by
  have H : (smoothPart n z : ℝ) * (roughPart n z : ℝ) = (n : ℝ) := by
    exact_mod_cast smoothPart_mul_roughPart n z
  have HL := congrArg Real.log H
  rw [Real.log_mul (by positivity) (by positivity)] at HL
  linarith

end NairTenenbaum
