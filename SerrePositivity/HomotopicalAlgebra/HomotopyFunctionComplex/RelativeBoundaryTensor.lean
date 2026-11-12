module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLifting
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor

/-! # Relative boundary tensors and actual relative latching maps -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  {A B : SimplexCategory ⥤ C} (α : A ⟶ B) (n : ℕ)

@[reassoc]
lemma boundaryTensorIso_naturality :
    HomPresentation.tensorSourceMap (SubcomplexTensor.diagram (SSet.boundary.{v} n)) α ≫
        (boundaryTensorIso B n).hom =
      (boundaryTensorIso A n).hom ≫
        (latchingEvaluation simplex (SimplexCategory.mk n)).map α := by
  apply colimit.hom_ext
  intro x
  change colimit.ι (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A) x ≫
      (HomPresentation.tensorSourceMap _ α ≫ (boundaryTensorIso B n).hom) =
    colimit.ι (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A) x ≫
      ((boundaryTensorIso A n).hom ≫
        colim.map (Functor.whiskerLeft (latchingSource simplex (SimplexCategory.mk n)) α))
  rw [← Category.assoc, HomPresentation.ι_tensorSourceMap, Category.assoc,
    ι_boundaryTensorIso_hom, ← Category.assoc, ι_boundaryTensorIso_hom]
  exact (colimit.ι_map
    (Functor.whiskerLeft (latchingSource simplex (SimplexCategory.mk n)) α)
    ((BoundaryIndex.toLatching.{v} n).obj x)).symm

abbrev relativeBoundaryTensorMap :=
  HomPresentation.relativeTensorMap (SubcomplexTensor.diagram (SSet.boundary.{v} n)) α
    (SubcomplexTensor.simplexCocone (SSet.boundary.{v} n))

abbrev relativeBoundaryPushoutMap :=
  pushout.map
    (HomPresentation.tensorSourceMap (SubcomplexTensor.diagram (SSet.boundary.{v} n)) α)
    (SubcomplexTensor.inclusion (SSet.boundary.{v} n) A)
    ((latchingEvaluation simplex (SimplexCategory.mk n)).map α)
    ((latchingComparison simplex (SimplexCategory.mk n)).app A)
    (boundaryTensorIso B n).hom (𝟙 (A.obj (SimplexCategory.mk n)))
    (boundaryTensorIso A n).hom (boundaryTensorIso_naturality α n)
    ((Category.comp_id _).trans (boundaryTensorIso_comparison A n))

instance relativeBoundaryPushoutMap_isIso : IsIso (relativeBoundaryPushoutMap α n) := by
  exact pushout.map_isIso _ _ _ _ (boundaryTensorIso B n).hom
    (𝟙 (A.obj (SimplexCategory.mk n))) (boundaryTensorIso A n).hom _ _

def relativeBoundaryTensorArrowIso : Arrow.mk (relativeBoundaryTensorMap α n) ≅
    Arrow.mk (relativeLatchingMap simplex (SimplexCategory.mk n) α) := by
  let e := asIso (relativeBoundaryPushoutMap α n)
  exact Arrow.isoMk e (Iso.refl _) (by
    change relativeBoundaryPushoutMap α n ≫
        relativeLatchingMap simplex (SimplexCategory.mk n) α =
      relativeBoundaryTensorMap α n ≫ 𝟙 _
    rw [Category.comp_id]
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, Category.assoc, inl_relativeLatchingMap]
      exact (boundaryTensorIso_comparison B n).symm.trans
        (HomPresentation.inl_relativeTensorMap _ α _).symm
    · rw [← Category.assoc, pushout.inr_desc, Category.assoc, inr_relativeLatchingMap,
        Category.id_comp]
      exact (HomPresentation.inr_relativeTensorMap
        (SubcomplexTensor.diagram (SSet.boundary.{v} n)) α
        (SubcomplexTensor.simplexCocone (SSet.boundary.{v} n))).symm)

lemma boundary_source_lifting [HasTerminal C] {Y : C}
    [HasLiftingProperty (relativeLatchingMap simplex (SimplexCategory.mk n) α) (terminal.from Y)] :
    HasLiftingProperty (SSet.boundary.{v} n).ι ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) := by
  have : HasLiftingProperty (relativeBoundaryTensorMap α n) (terminal.from Y) :=
    (HasLiftingProperty.iff_of_arrow_iso_left (relativeBoundaryTensorArrowIso α n)
      (terminal.from Y)).mpr inferInstance
  have h := HomPresentation.source_hasLiftingProperty
    (SubcomplexTensor.diagram (SSet.boundary.{v} n))
    (NonsingularPresentation.cocone (SSet.boundary.{v} n).toSSet)
    (NonsingularPresentation.isColimit (SSet.boundary.{v} n).toSSet) α
    (SubcomplexTensor.simplexCocone (SSet.boundary.{v} n)) (Y := Y)
  rwa [SubcomplexTensor.presentationMap_eq] at h

end SerrePositivity.HomotopyFunctionComplex
