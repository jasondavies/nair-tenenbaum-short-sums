module

public import NairTenenbaum.Arithmetic

@[expose] public section

/-! # Smooth parametrization of coordinate faces of a cube -/

open scoped Classical

namespace NairTenenbaum

variable {ι : Type*} [Fintype ι]

theorem card_coordinateFaceParameter (i : ι) :
    Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl (fun j => j = i)]
  simp

noncomputable def coordinateFaceParameterEquiv (i : ι) :
    {j : ι // j ≠ i} ≃ Fin (Fintype.card ι - 1) :=
  Fintype.equivFinOfCardEq (card_coordinateFaceParameter i)

noncomputable def cubeFaceMap (i : ι) (b : ℝ) (v : Fin (Fintype.card ι - 1) → ℝ) : ι → ℝ :=
  fun j => if h : j = i then b else v (coordinateFaceParameterEquiv i ⟨j, h⟩)

theorem contDiff_cubeFaceMap (i : ι) (b : ℝ) : ContDiff ℝ ⊤ (cubeFaceMap i b) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = i
  · simp only [cubeFaceMap, hj, ↓reduceDIte]
    fun_prop
  · simp only [cubeFaceMap, hj, ↓reduceDIte]
    fun_prop

theorem cubeFaceMap_mem_cube (i : ι) {b : ℝ} (hb : b ∈ Set.Icc 0 1)
    {v : Fin (Fintype.card ι - 1) → ℝ}
    (hv : v ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)) :
    cubeFaceMap i b v ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
  constructor <;> intro j <;> by_cases hj : j = i
  · simpa only [cubeFaceMap, hj, ↓reduceDIte] using hb.1
  · simpa only [cubeFaceMap, hj, ↓reduceDIte] using hv.1 (coordinateFaceParameterEquiv i ⟨j, hj⟩)
  · simpa only [cubeFaceMap, hj, ↓reduceDIte] using hb.2
  · simpa only [cubeFaceMap, hj, ↓reduceDIte] using hv.2 (coordinateFaceParameterEquiv i ⟨j, hj⟩)

theorem exists_cubeFaceMap_of_coordinate_eq {i : ι} {b : ℝ} {v : ι → ℝ}
    (hv : v ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)) (hi : v i = b) :
    ∃ u : Fin (Fintype.card ι - 1) → ℝ,
      u ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) ∧ cubeFaceMap i b u = v := by
  let u := fun k : Fin (Fintype.card ι - 1) => v ((coordinateFaceParameterEquiv i).symm k).1
  refine ⟨u, ⟨fun k => hv.1 _, fun k => hv.2 _⟩, ?_⟩
  ext j
  by_cases hj : j = i
  · subst j
    simp [cubeFaceMap, hi]
  · simp [cubeFaceMap, hj, u]

end NairTenenbaum
