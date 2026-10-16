module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt

/-! # The prescribed all-degree degeneracies restrict to the actual boundary

Agreement on every facet follows from the mixed identities. Joint boundary
extensionality then gives equality of whole functors, without faithfulness
of any individual face restriction or of the base projection.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary
open FreeGeneratorCategories FreeGeneratorMixedOperators OrdinaryBarFreeDiagramExtension
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues
open OrdinaryBarFreeResolutionMixedFaces
open SerrePositivity.SimplicialModel.ReversedSimplexParameters
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

include degeneracyLaw in
lemma boundary_degeneracy_facet (j : Fin (n + 2)) (k : Fin (n + 3)) :
    (degeneracyFunctor D (n + 1) j ⋙
      OrdinaryBarFreeResolutionBoundary.boundary hcof hfib D n P F G faceLaw) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) =
    (diagram hcof hfib D n P F j ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.boundary (n + 2)).ι)) ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) := by
  rw [CategoryTheory.Functor.assoc, OrdinaryBarFreeResolutionBoundary.boundary_face,
    CategoryTheory.Functor.assoc, ← OrdinaryBarChoiceCategory.reindex_comp,
    ← whiskerLeft_comp, SSet.boundary.ι_ι]
  simpa only [OrdinaryBarFreeResolutionBoundary.face, rawFace, delta_eq, Fin.rev_rev] using
    facet_equation hcof hfib D n P F G faceLaw degeneracyLaw j k.rev

include degeneracyLaw in
lemma boundary_degeneracy (j : Fin (n + 2)) :
    degeneracyFunctor D (n + 1) j ⋙
      OrdinaryBarFreeResolutionBoundary.boundary hcof hfib D n P F G faceLaw =
    diagram hcof hfib D n P F j ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.boundary (n + 2)).ι) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply OrdinaryBarChoiceBoundaryExt.hom_ext hcof hfib _ _
  intro k
  exact congr($(boundary_degeneracy_facet hcof hfib D n P F G faceLaw degeneracyLaw j k).map f)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary
