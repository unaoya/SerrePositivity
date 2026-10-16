module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension

/-! # Raise the degree of the coherent free choice diagram

Two consecutive choice functors satisfying the lower face and degeneracy
equations determine a next functor satisfying every required face and
degeneracy equation. The overlap and boundary restrictions are derived,
rather than supplied as extra assumptions to the relative filler.
-/

@[expose] public section
universe v u vD uD r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep
open FreeGeneratorCategories FreeGeneratorDegeneracies OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues

abbrev inclusion (n : ℕ) (P : SSet.{r}) := P ◁ (SSet.boundary (n + 2)).ι

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (faceLaw : ∀ i : Fin (n + 2), F ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      FreeGeneratorFaces.fixedFace D (n + 1) i ⋙ G)
  (degeneracyLaw : ∀ i : Fin (n + 1), degeneracyFunctor D n i ⋙ F =
    G ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma n i))

abbrev boundaryDiagram := OrdinaryBarFreeResolutionBoundary.boundary hcof hfib D n P F G faceLaw

def boundaryGenerators : degree D (n + 2) ⥤q
    target (C := C) hcof hfib (P ⊗ (SSet.boundary (n + 2)).toSSet) :=
  Paths.of (degree D (n + 2)) ⋙q (boundaryDiagram hcof hfib D n P F G faceLaw).toPrefunctor

include degeneracyLaw in
lemma value_restriction (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y) :
    (OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P)).map
      (value hcof hfib D n P F i p) =
    (boundaryGenerators hcof hfib D n P F G faceLaw).map (degeneracy (n + 1) i p) := by
  change (OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P)).map
      ((diagram hcof hfib D n P F i).map (singleton (n + 1) p)) =
    (boundaryDiagram hcof hfib D n P F G faceLaw).map
      (singleton (n + 2) (degeneracy (n + 1) i p))
  have hh := congr($(OrdinaryBarFreeResolutionDegenerateBoundary.boundary_degeneracy
    hcof hfib D n P F G faceLaw degeneracyLaw i).map (singleton (n + 1) p))
  simpa only [CategoryTheory.Functor.comp_map, degeneracyFunctor_generator] using hh.symm

def filler : degree D (n + 3) ⥤ target (C := C) hcof hfib (parameters P (n + 2)) :=
  OrdinaryBarFreeDegeneracyExtension.filler hcof hfib D n (inclusion n P)
    (boundaryGenerators hcof hfib D n P F G faceLaw) (value hcof hfib D n P F)
    (value_restriction hcof hfib D n P F G faceLaw degeneracyLaw)

lemma filler_boundary : filler hcof hfib D n P F G faceLaw degeneracyLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P) =
      boundaryDiagram hcof hfib D n P F G faceLaw := by
  rw [filler, OrdinaryBarFreeDegeneracyExtension.filler_boundary]
  exact (Paths.lift_unique (V := degree D (n + 2)) _
    (boundaryDiagram hcof hfib D n P F G faceLaw) rfl).symm

lemma filler_face (k : Fin (n + 3)) : filler hcof hfib D n P F G faceLaw degeneracyLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ k) =
      FreeGeneratorFaces.fixedFace D (n + 2) k ⋙ F := by
  rw [← SSet.boundary.ι_ι k, whiskerLeft_comp, OrdinaryBarChoiceCategory.reindex_comp,
    ← CategoryTheory.Functor.assoc]
  change (filler hcof hfib D n P F G faceLaw degeneracyLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (inclusion n P)) ⋙ _ = _
  rw [filler_boundary]
  exact OrdinaryBarFreeResolutionBoundary.boundary_face hcof hfib D n P F G faceLaw k

lemma filler_degeneracy (i : Fin (n + 2)) : degeneracyFunctor D (n + 1) i ⋙
    filler hcof hfib D n P F G faceLaw degeneracyLaw =
      F ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma (n + 1) i) := by
  rw [filler, OrdinaryBarFreeDegeneracyExtension.filler_degeneracy hcof hfib D n _ _ _
    (values_compatible hcof hfib D n P F G degeneracyLaw) _ i]
  exact diagram_from_generators hcof hfib D n P F i

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep
