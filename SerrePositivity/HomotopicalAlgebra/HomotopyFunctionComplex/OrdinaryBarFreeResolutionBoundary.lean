module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing

/-! # The actual next free-resolution boundary from the preceding face equations

The source faces are the fixed-object reversed faces of the existing comonad
resolution. Their relations imply every boundary overlap; these overlaps are
proved here, not additional data in the construction.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary
open OrdinaryBarFreeDiagramExtension FreeGeneratorCategories FreeGeneratorDegeneracies
open FreeGeneratorFaces OrdinaryBarChoiceBoundaryGluing
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (faceLaw : ∀ i : Fin (n + 2), F ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      fixedFace D (n + 1) i ⋙ G)

def face (k : Fin (n + 3)) :
    degree D (n + 3) ⥤ target (C := C) hcof hfib (parameters P (n + 1)) :=
  fixedFace D (n + 2) k ⋙ F

include faceLaw in
lemma face_overlap (j k : Fin (n + 3)) (hjk : j < k) :
    face hcof hfib D n P F j ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk))) =
    face hcof hfib D n P F k ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk))) := by
  rw [face, face, CategoryTheory.Functor.assoc, CategoryTheory.Functor.assoc,
    faceLaw, faceLaw, ← CategoryTheory.Functor.assoc, ← CategoryTheory.Functor.assoc,
    fixedFace_overlap D (n + 1) j k hjk]

def seed : degree D (n + 2) ⥤q target (C := C) hcof hfib (parameters P (n + 1)) :=
  Paths.of (degree D (n + 2)) ⋙q (face hcof hfib D n P F 0).toPrefunctor

def faceValues (k : Fin (n + 3)) {X Y : degree D (n + 2)} (e : X ⟶ Y) :
    (seed hcof hfib D n P F).obj X ⟶ (seed hcof hfib D n P F).obj Y :=
  (face hcof hfib D n P F k).map e.toPath

include faceLaw in
lemma values_compatible {X Y : degree D (n + 2)} (e : X ⟶ Y) :
    Compatible hcof hfib n (fun k => faceValues hcof hfib D n P F k e) := by
  intro j k hjk
  exact congr($(face_overlap hcof hfib D n P F G faceLaw j k hjk).map e.toPath)

def boundary : degree D (n + 3) ⥤
    target (C := C) hcof hfib (P ⊗ (SSet.boundary (n + 2)).toSSet) :=
  OrdinaryBarFreeBoundaryGluing.boundary (V := degree D (n + 2)) hcof hfib n
    (seed hcof hfib D n P F) (faceValues hcof hfib D n P F)
    (values_compatible hcof hfib D n P F G faceLaw)

lemma boundary_face (k : Fin (n + 3)) : boundary hcof hfib D n P F G faceLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) =
      face hcof hfib D n P F k := by
  rw [boundary, OrdinaryBarFreeBoundaryGluing.boundary_face]
  exact (Paths.lift_unique (V := degree D (n + 2)) _ (face hcof hfib D n P F k) rfl).symm

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary
