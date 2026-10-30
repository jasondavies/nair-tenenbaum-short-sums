/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import NairTenenbaum

/-!
# Palomar solution

The submission definitions and propositions repeat the independent Challenge.
Every theorem below follows from its proved library counterpart by definitional
equality. The shared arithmetic and polynomial structures are the library's
original types; there are no extra analytic assumptions or definition holes.
This module does not import Challenge.
-/

@[expose] public section

namespace NairTenenbaum.Submission

open Finset Polynomial Real

noncomputable def sieveProduct (Q : ℤ[X]) (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 - (rootCount Q p : ℝ) / p)

def substitute {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) : Tuple k :=
  fun j => ∏ h, n h ^ γ j h

def weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) : ℕ :=
  ∏ h, (n h : ℕ) ^ totalExponent γ h

def pullback {k r : ℕ} (γ : Fin k → Fin r → ℕ) (H : ArithmeticMap k) : ArithmeticMap r :=
  fun n => H (substitute γ n)

def Dagger {r : ℕ} (D : ℕ) (n : Tuple r) : Prop :=
  (∀ i j, i ≠ j → Nat.Coprime (n i) (n j)) ∧ ∀ i, Nat.Coprime (n i) D

def tupleBox (r : ℕ) (N : ℕ+) : Finset (Tuple r) :=
  Fintype.piFinset fun _ => Finset.Icc 1 N

noncomputable def weightFiber {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ) (N : ℕ+) :
    Finset (Tuple r) := by
  classical
  exact (tupleBox r N).filter fun n => weightedMass γ n = N ∧ Dagger D n

noncomputable def weight {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ)
    (F : ArithmeticMap k) (θ : Fin r → ℕ → ℝ) (N : ℕ+) : ℝ :=
  ∑ n ∈ weightFiber γ D N, pullback γ F n * ∏ h, θ h (n h) / (n h : ℝ)

noncomputable def systemTotal {k r : ℕ} (P : PolynomialSystem k r) : ℤ[X] := ∏ j, P.Q j

noncomputable def systemRadical {k r : ℕ} (P : PolynomialSystem k r) : ℤ[X] := ∏ h, P.R h

noncomputable def systemDiscriminant {k r : ℕ} (P : PolynomialSystem k r) : ℕ :=
  (systemRadical P).discr.natAbs

noncomputable def systemBadDiscriminant {k r : ℕ} (P : PolynomialSystem k r) : ℕ :=
  ∏ p ∈ (systemDiscriminant P).primeFactors.filter (fun p => rootCount (systemTotal P) p ≠ 0),
    p ^ (systemDiscriminant P).factorization p

noncomputable def systemRootVector {k r : ℕ} (P : PolynomialSystem k r) (h : Fin r) (n : ℕ) : ℝ :=
  rootCount (P.R h) n

noncomputable def systemWeight {k r : ℕ} (P : PolynomialSystem k r) (F : ArithmeticMap k)
    (N : ℕ+) : ℝ := weight P.exponent (systemDiscriminant P) F (systemRootVector P) N

/-! ## Height, finite intervals, and the main term (equation (18)) -/

def polynomialHeight (Q : ℤ[X]) : ℕ := Q.support.sup fun i => (Q.coeff i).natAbs

noncomputable def extendArithmeticMap {k : ℕ} (F : ArithmeticMap k) (n : Fin k → ℕ) : ℝ :=
  if h : ∀ j, 0 < n j then F (fun j => ⟨n j, h j⟩) else 0

noncomputable def shortInterval (x y : ℝ) : Finset ℕ := Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊

noncomputable def shortSum {k : ℕ} (Q : Fin k → ℤ[X]) (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, extendArithmeticMap F (fun j => ((Q j).eval (n : ℤ)).natAbs)

noncomputable def positiveUpTo (x : ℝ) : Finset ℕ+ :=
  (Finset.Icc 1 (Nat.toPNat' ⌊x⌋₊)).filter fun n => (n : ℝ) ≤ x

noncomputable def mainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  y * sieveProduct (systemTotal P) x * ∑ n ∈ positiveUpTo x, (systemWeight P) F n

/-! ## Theorem 1: uniform short sums at polynomial values -/

def TheoremOne : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (P : PolynomialSystem k r), (systemTotal P).natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
          ∀ (x y : ℝ), c₀ * (polynomialHeight (systemTotal P) : ℝ) ^ δ < x →
            x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
            shortSum P.Q F x y ≤ C (systemBadDiscriminant P) * mainTerm P F x y

theorem theoremOne : TheoremOne := NairTenenbaum.theoremOne

/-! ## Theorem 2: greatest prime factor, with no fixed-prime restriction -/

noncomputable def polynomialValueProduct (Q : ℤ[X]) (x y : ℝ) : ℕ :=
  ∏ n ∈ shortInterval x y, (Q.eval (n : ℤ)).natAbs

noncomputable def polynomialGreatestPrimeFactor (Q : ℤ[X]) (x y : ℝ) : ℕ :=
  Nat.maxPrimeFac (polynomialValueProduct Q x y)

def TheoremTwo : Prop :=
  ∀ Q : ℤ[X], Irreducible Q → 0 < Q.natDegree →
    ∀ k : ℕ, Q.natDegree < k → ∀ α : ℝ, α < 2 - Real.log 4 →
      ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ < x →
        let y : ℝ := x ^ ((Q.natDegree : ℝ) / k)
        y * Real.exp ((Real.log x) ^ α) < (polynomialGreatestPrimeFactor Q x y : ℝ)

theorem theoremTwo : TheoremTwo := NairTenenbaum.theoremTwo

/-! ## Theorem 3: sums at prime arguments, with constant-term correction -/

noncomputable def totientTwist (g n : ℕ) : ℝ := ((n : ℝ) / n.totient) ^ g

noncomputable def primeShortSum {k : ℕ} (Q : Fin k → ℤ[X])
    (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  ∑ p ∈ (shortInterval x y).filter Nat.Prime,
    extendArithmeticMap F (fun j => ((Q j).eval (p : ℤ)).natAbs)

noncomputable def primeArgumentFactor (Q : ℤ[X]) (z : ℝ) : ℝ :=
  totientTwist 1 (Q.eval 0).natAbs / Real.log z

noncomputable def primeMainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  mainTerm P F x y * primeArgumentFactor (systemTotal P) x

def TheoremThree : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (P : PolynomialSystem k r), (systemTotal P).natDegree = g → (systemTotal P).eval 0 ≠ 0 →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
          ∀ x y : ℝ, c₀ * (polynomialHeight (systemTotal P) : ℝ) ^ δ < x →
            x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
            primeShortSum P.Q F x y ≤ C (systemBadDiscriminant P) * primeMainTerm P F x y

theorem theoremThree : TheoremThree := NairTenenbaum.theoremThree

/-! ## Progression and product main terms -/

noncomputable def progressionSieveProduct (Q : ℤ[X]) (q : ℕ) (x : ℝ) : ℝ :=
  ∏ p ∈ ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).filter (fun p => ¬p ∣ q),
    (1 - (rootCount Q p : ℝ) / p)

noncomputable def progressionSum {k : ℕ} (Q : Fin k → Polynomial ℤ) (F : ArithmeticMap k)
    (q a : ℕ) (x y : ℝ) : ℝ :=
  ∑ n ∈ (shortInterval x y).filter (fun n => Nat.ModEq q n a),
    extendArithmeticMap F (fun j => ((Q j).eval (n : ℤ)).natAbs)

noncomputable def progressionMainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (q : ℕ) (x y : ℝ) : ℝ :=
  (y / q) * progressionSieveProduct (systemTotal P) q x *
    ∑ N ∈ (positiveUpTo x).filter (fun N : ℕ+ => Nat.Coprime q N), (systemWeight P) F N

noncomputable def irreducibleBadDiscriminant {k : ℕ} (Q : Fin k → Polynomial ℤ) : ℕ :=
  let T := ∏ j, Q j
  let D := T.discr.natAbs
  ∏ p ∈ D.primeFactors.filter (fun p => rootCount T p ≠ 0), p ^ D.factorization p

noncomputable def irreducibleProgressionTuples (k D q : ℕ) (x : ℝ) : Finset (Tuple k) := by
  classical
  exact (tupleBox k (Nat.toPNat' ⌊x⌋₊)).filter (fun n => (mass n : ℝ) ≤ x ∧ Dagger (D * q) n)

noncomputable def irreducibleProgressionMainTerm {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (F : ArithmeticMap k) (q : ℕ) (x y : ℝ) : ℝ :=
  (y / q) * progressionSieveProduct (∏ j, Q j) q x *
    ∑ n ∈ irreducibleProgressionTuples k (∏ j, Q j).discr.natAbs q x,
      F n * ∏ j, (rootCount (Q j) (n j) : ℝ) / (n j : ℝ)

noncomputable def rootWeightedSum (Q : Polynomial ℤ) (F : ArithmeticMap 1) (x : ℝ) : ℝ :=
  ∑ n ∈ positiveUpTo x, F (fun _ => n) * ((rootCount Q n : ℝ) / (n : ℝ))

noncomputable def factoredMainTerm {k r : ℕ} (P : PolynomialSystem k r)
    (F : Fin k → ArithmeticMap 1) (x y : ℝ) : ℝ :=
  y * sieveProduct (systemTotal P) x * ∏ j, rootWeightedSum (P.Q j) (F j) x

noncomputable def productShortSum {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (F : Fin k → ArithmeticMap 1) (x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, ∏ j, extendArithmeticMap (F j) (fun _ => ((Q j).eval (n : ℤ)).natAbs)

/-! ## Corollary 1: arithmetic progressions -/

def CorollaryOne : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 / (2 * (g : ℝ)) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ β : ℝ, 0 < β → β < 1 →
      ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
        ∀ (P : PolynomialSystem k r), (systemTotal P).natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * β * δ / 6) F →
        ∀ (q a : ℕ), 0 < q → 0 < a → a ≤ q → q.Coprime ((systemTotal P).eval (a : ℤ)).natAbs →
        ∀ (x y : ℝ), c₁ * (polynomialHeight (systemTotal P) : ℝ) ^ (2 * δ) < x →
          x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x → (q : ℝ) ≤ y ^ (1 - β) →
          progressionSum P.Q F q a x y ≤ C (systemBadDiscriminant P) * progressionMainTerm P F q x y

theorem corollaryOne : CorollaryOne := NairTenenbaum.corollaryOne

/-! ## Corollary 2: irreducible pairwise coprime polynomials -/

def CorollaryTwo : Prop :=
  ∀ (k g : ℕ), 0 < k → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 / (2 * (g : ℝ)) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ β : ℝ, 0 < β → β < 1 →
      ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
        ∀ (Q : Fin k → Polynomial ℤ), (∀ j, Irreducible (Q j)) →
        (∀ i j, i ≠ j → IsCoprime ((Q i).map (Int.castRingHom ℚ)) ((Q j).map (Int.castRingHom ℚ))) →
        NoFixedPrimeDivisor (∏ j, Q j) → (∏ j, Q j).natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * β * δ / 6) F →
        ∀ (q a : ℕ), 0 < q → 0 < a → a ≤ q → q.Coprime ((∏ j, Q j).eval (a : ℤ)).natAbs →
        ∀ (x y : ℝ), c₁ * (polynomialHeight (∏ j, Q j) : ℝ) ^ (2 * δ) < x →
          x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x → (q : ℝ) ≤ y ^ (1 - β) →
          progressionSum Q F q a x y ≤ C (irreducibleBadDiscriminant Q) *
            irreducibleProgressionMainTerm Q F q x y

theorem corollaryTwo : CorollaryTwo := NairTenenbaum.corollaryTwo

/-! ## Corollary 3: products of scalar arithmetic functions -/

def CorollaryThree : Prop :=
  ∀ (k g : ℕ), 0 < k → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (r : ℕ) (P : PolynomialSystem k r), (systemTotal P).natDegree = g →
      (∀ i j, i ≠ j → IsCoprime ((P.Q i).map (Int.castRingHom ℚ)) ((P.Q j).map (Int.castRingHom ℚ))) →
      ∀ (F : Fin k → ArithmeticMap 1), (∀ j, Admissible A B (ε * δ / 3) (F j)) →
      ∀ (x y : ℝ), c₀ * (polynomialHeight (systemTotal P) : ℝ) ^ δ < x →
        x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
        productShortSum P.Q F x y ≤ C (systemBadDiscriminant P) * factoredMainTerm P F x y

theorem corollaryThree : CorollaryThree := NairTenenbaum.corollaryThree

/-! ## Hooley divisor concentration and the explicit subexponential factor -/

noncomputable def divisorWindow (n : ℕ) (u : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => u < log d ∧ log d ≤ u + 1).card

noncomputable def hooleyDelta (n : ℕ) : ℕ := sSup (Set.range (divisorWindow n))

noncomputable def hooleyPolynomialSum (Q : ℤ[X]) (t x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, (hooleyDelta (Q.eval (n : ℤ)).natAbs : ℝ) ^ t

noncomputable def hooleyRootSum (Q : ℤ[X]) (t x : ℝ) : ℝ :=
  ∑ n ∈ positiveUpTo x, (hooleyDelta n : ℝ) ^ t * ((rootCount Q n : ℝ) / (n : ℝ))

noncomputable def hooleySubexponential (η x : ℝ) : ℝ :=
  Real.exp (η * Real.sqrt (Real.log (Real.log x) * Real.log (Real.log (Real.log x))))

noncomputable def dyadicFloorSum (D x y : ℝ) : ℝ :=
  ∑ d ∈ shortInterval D D,
    (((⌊(x + y) / d⌋ : ℤ) : ℝ) - ((⌊x / d⌋ : ℤ) : ℝ))

/-! ## Corollary 4: Hooley moments at polynomial values -/

def CorollaryFour : Prop :=
  ∀ Q : ℤ[X], NoFixedPrimeDivisor Q → Irreducible Q →
    ∀ t ε η : ℝ, 1 ≤ t → 0 < ε → Real.sqrt (2 * t) < η →
      ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ x y : ℝ,
        x₀ < x → x ^ ε ≤ y → y ≤ x →
          hooleyPolynomialSum Q t x y ≤
            C * (y * (Real.log x) ^ ((2 : ℝ) ^ t - t - 1) * hooleySubexponential η x)

theorem corollaryFour : CorollaryFour := NairTenenbaum.corollaryFour

/-! ## Corollary 5: dyadic floor-difference averages -/

def CorollaryFive : Prop :=
  ∀ ε η : ℝ, 0 < ε → ε < 1 → Real.sqrt 2 < η →
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ D x y : ℝ,
      1 ≤ D → x₀ < x → x ^ ε ≤ y → y ≤ x →
        dyadicFloorSum D x y ≤ C * (y * hooleySubexponential η x)

theorem corollaryFive : CorollaryFive := NairTenenbaum.corollaryFive

/-! ## Corollary 6: smooth values, with explicit nonconstancy -/

noncomputable def smoothShortSum {k : ℕ} (Q : Fin k → ℤ[X]) (F : ArithmeticMap k)
    (j : Fin k) (x y z : ℝ) : ℝ :=
  ∑ n ∈ (shortInterval x y).filter (fun n : ℕ =>
    ((Q j).eval (n : ℤ)).natAbs ∈ Nat.factoredNumbers (Icc 0 ⌊z⌋₊)),
      extendArithmeticMap F (fun i => ((Q i).eval (n : ℤ)).natAbs)

def CorollarySix : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ κ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 → 0 < κ →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (P : PolynomialSystem k r), (systemTotal P).natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 4) F →
      ∀ (j : Fin k), 0 < (P.Q j).natDegree → ∀ (x y z : ℝ),
      c₀ * (polynomialHeight (systemTotal P) : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      (2 : ℝ) ^ (κ / (2 * (g : ℝ) ^ 2 * ε)) ≤ z → z ≤ x →
      smoothShortSum P.Q F j x y z ≤
        C (systemBadDiscriminant P) * Real.exp (-κ * Real.log x / Real.log z) * mainTerm P F x y

theorem corollarySix : CorollarySix := NairTenenbaum.corollarySix

/-! ## Corollary 7: shifted primes, with corrected interval range -/

noncomputable def shiftedPrimeSum (a : ℤ) (F : ArithmeticMap 1) (x y : ℝ) : ℝ :=
  ∑ p ∈ (shortInterval x y).filter Nat.Prime,
    extendArithmeticMap F (fun _ => ((p : ℤ) + a).natAbs)

noncomputable def shiftedPrimeMainTerm (a : ℤ) (F : ArithmeticMap 1) (x y : ℝ) : ℝ :=
  ((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
    ∑ n ∈ positiveUpTo x, F (fun _ => n) / (n : ℝ)

def CorollarySeven : Prop :=
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / 8 → 0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℤ), a ≠ 0 → ∀ (F : ArithmeticMap 1), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (a.natAbs : ℝ) ^ δ < x → x ^ (4 * ε) ≤ y → y ≤ x →
        shiftedPrimeSum a F x y ≤ C * shiftedPrimeMainTerm a F x y

theorem corollarySeven : CorollarySeven := NairTenenbaum.corollarySeven

/-! ## Corollaries 8–9: Hooley and progression averages over primes -/

noncomputable def hooleyPrimeSum (a : ℤ) (t x y : ℝ) : ℝ :=
  ∑ p ∈ (shortInterval x y).filter Nat.Prime,
    (hooleyDelta ((p : ℤ) + a).natAbs : ℝ) ^ t

noncomputable def primeProgressionCount (x : ℝ) (q : ℕ) (a : ℤ) : ℕ :=
  ((Icc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ Int.ModEq (q : ℤ) (p : ℤ) a)).card

noncomputable def dyadicPrimeProgressionSum (K : ℝ) (a : ℤ) (x y : ℝ) : ℝ :=
  ∑ q ∈ shortInterval K K,
    ((primeProgressionCount (x + y) q a : ℝ) - (primeProgressionCount x q a : ℝ))

def CorollaryEight : Prop :=
  ∀ ε η : ℝ, 0 < ε → ε < 1 → Real.sqrt 2 < η →
    ∃ x₀ C D : ℝ, 1 < x₀ ∧ 0 < C ∧ 0 < D ∧ ∀ a : ℤ, a ≠ 0 → ∀ x y : ℝ,
      x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ ε ≤ y → y ≤ x →
        hooleyPrimeSum a 1 x y ≤ C *
          (((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
            hooleyRootSum (X : ℤ[X]) 1 x) ∧
        ((a.natAbs : ℝ) / a.natAbs.totient) * (y / (Real.log x) ^ 2) *
            hooleyRootSum (X : ℤ[X]) 1 x ≤ D * (y / Real.log x * hooleySubexponential η x)

theorem corollaryEight : CorollaryEight := NairTenenbaum.corollaryEight

def CorollaryNine : Prop :=
  ∀ ε η : ℝ, 0 < ε → ε < 1 → Real.sqrt 2 < η →
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ a : ℤ, a ≠ 0 → ∀ K x y : ℝ,
      0 < K → x₀ < x → (a.natAbs : ℝ) ≤ x → x ^ ε ≤ y → y ≤ x →
        dyadicPrimeProgressionSum K a x y ≤ C * (y / Real.log x * hooleySubexponential η x)

theorem corollaryNine : CorollaryNine := NairTenenbaum.corollaryNine

/-! ## Corollary 10: Goldbach with one prime in a short interval -/

noncomputable def goldbachPrimes (N : ℕ) (x y : ℝ) : Finset ℕ :=
  (shortInterval x y).filter (fun p => p.Prime ∧ (N - p).Prime)

noncomputable def goldbachCount (N : ℕ) (x y : ℝ) : ℕ :=
  (goldbachPrimes N x y).card

def CorollaryTen : Prop :=
  ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 < N → ∀ (x y : ℝ),
      (N : ℝ) ^ δ < x → x ^ ε ≤ y → y ≤ x →
      (goldbachCount N x y : ℝ) ≤ C * (((N : ℝ) / N.totient) * y / (Real.log N) ^ 2)

theorem corollaryTen : CorollaryTen := NairTenenbaum.corollaryTen

/-! ## Lemma 2: general class-M weights and convergent smooth tails -/

def ScalarClassM (θ : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 1 ≤ B ∧
    Admissible A B ε (fun n : Tuple 1 => θ (n 0))

def LemmaTwo : Prop :=
  ∀ (k r g : ℕ), 0 < g →
    ∀ (γ : Fin k → Fin r → ℕ), (∀ i, 0 < totalExponent γ i) →
      (∀ i, totalExponent γ i ≤ g) →
    ∀ (A B ε δ κ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
      0 < δ → δ ≤ 1 → 0 < κ →
    ∀ (θ : Fin r → ℕ → ℝ), (∀ i, ScalarClassM (θ i)) →
      ∃ C : ℝ, 0 < C ∧ ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
        ∀ (D : ℕ) (x z : ℝ), z < x →
          (4 : ℝ) ^ (((∑ i, totalExponent γ i : ℕ) : ℝ) * κ) < z →
          let f := fun m : ℕ+ =>
            if (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)
            then weight γ D F θ m else 0
          Summable f ∧ (∑' m, f m) ≤
            C * Real.exp (-κ * Real.log x / Real.log z) *
              ∑ m ∈ positiveUpTo z, weight γ D F θ m

theorem lemmaTwo : LemmaTwo := NairTenenbaum.lemmaTwo
end NairTenenbaum.Submission
