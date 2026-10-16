module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep

/-! # Iterate the relative free-resolution step with all coherence equations

A coherent initial pair determines actual choice functors in every degree.
The face and degeneracy equations are retained as fields at each step, so
independent filler existence is not being substituted for coherent choices.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower
open FreeGeneratorCategories OrdinaryBarFreeDiagramExtension OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarFreeResolutionDegeneracyValues
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (P : SSet.{max u v})

structure Pair (n : ℕ) where
  current : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1))
  previous : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n)
  faceLaw : ∀ i : Fin (n + 2), current ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      FreeGeneratorFaces.fixedFace D (n + 1) i ⋙ previous
  degeneracyLaw : ∀ i : Fin (n + 1), degeneracyFunctor D n i ⋙ current =
    previous ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma n i)

def next {n : ℕ} (A : Pair (C := C) hcof hfib D P n) : Pair (C := C) hcof hfib D P (n + 1) where
  current := OrdinaryBarFreeResolutionStep.filler hcof hfib D n P A.current A.previous
    A.faceLaw A.degeneracyLaw
  previous := A.current
  faceLaw := OrdinaryBarFreeResolutionStep.filler_face hcof hfib D n P A.current A.previous
    A.faceLaw A.degeneracyLaw
  degeneracyLaw := OrdinaryBarFreeResolutionStep.filler_degeneracy hcof hfib D n P
    A.current A.previous A.faceLaw A.degeneracyLaw

lemma next_previous {n : ℕ} (A : Pair (C := C) hcof hfib D P n) :
    (next hcof hfib D P A).previous = A.current := rfl

def iterate {n : ℕ} (A : Pair (C := C) hcof hfib D P n) :
    (k : ℕ) → Pair (C := C) hcof hfib D P (n + k)
  | 0 => A
  | k + 1 => next hcof hfib D P (iterate A k)

lemma iterate_succ {n : ℕ} (A : Pair (C := C) hcof hfib D P n) (k : ℕ) :
    iterate hcof hfib D P A (k + 1) = next hcof hfib D P (iterate hcof hfib D P A k) := rfl

/-- A coherent pair in degrees zero and one, on the actual fixed-object resolution. -/
abbrev Seed := Pair (C := C) hcof hfib D P 0

variable (A : Seed (C := C) hcof hfib D P)

def fromSeed : (m : ℕ) → Pair (C := C) hcof hfib D P m
  | 0 => A
  | m + 1 => next hcof hfib D P (fromSeed m)

/-- The whole sequence, including the seed's original degree-zero functor. -/
def diagram : (m : ℕ) →
    (degree D (m + 1) ⥤ target (C := C) hcof hfib (parameters P m))
  | 0 => A.previous
  | m + 1 => (fromSeed hcof hfib D P A m).current

lemma diagram_zero : diagram hcof hfib D P A 0 = A.previous := rfl

lemma diagram_one : diagram hcof hfib D P A 1 = A.current := rfl

lemma diagram_face (m : ℕ) (i : Fin (m + 2)) : diagram hcof hfib D P A (m + 1) ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      FreeGeneratorFaces.fixedFace D (m + 1) i ⋙ diagram hcof hfib D P A m := by
  cases m with
  | zero => exact A.faceLaw i
  | succ m => exact (fromSeed hcof hfib D P A (m + 1)).faceLaw i

lemma diagram_degeneracy (m : ℕ) (i : Fin (m + 1)) : degeneracyFunctor D m i ⋙
    diagram hcof hfib D P A (m + 1) = diagram hcof hfib D P A m ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma m i) := by
  cases m with
  | zero => exact A.degeneracyLaw i
  | succ m => exact (fromSeed hcof hfib D P A (m + 1)).degeneracyLaw i

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower
