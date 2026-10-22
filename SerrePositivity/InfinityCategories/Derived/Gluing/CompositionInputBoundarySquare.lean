module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputBoundaryNaturality

/-! 第一辺と対角辺の同時評価は、元の三角形の全境界制限と可換。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)

def dgGluingCompositionInputDiagonal : compositionCorrespondence x g ⟶
    intervalMappingSpace x y ⊗ intervalMappingSpace x z :=
  CartesianMonoidalCategory.lift (compositionCorrespondenceFirst x g)
    (compositionCorrespondenceDiagonal x g)

lemma dgGluingCompositionInputDiagonal_first :
    dgGluingCompositionInputDiagonal x g ≫ fst _ _ = compositionCorrespondenceFirst x g :=
  CartesianMonoidalCategory.lift_fst _ _

lemma dgGluingCompositionInputDiagonal_diagonal :
    dgGluingCompositionInputDiagonal x g ≫ snd _ _ = compositionCorrespondenceDiagonal x g :=
  CartesianMonoidalCategory.lift_snd _ _

lemma dgGluingCompositionInputBoundarySquare :
    pullback.fst ((pre (horn 2 1).ι).app X) (composableHomHornMap x g) ≫
        (pre (boundary 2).ι).app X =
      dgGluingCompositionInputDiagonal x g ≫ dgGluingCompositionInputBoundaryMap x g := by
  apply uncurry_injective
  rw [uncurry_pre_app, dgGluingCompositionInputBoundaryMap_uncurry,
    dgGluingCompositionInputDiagonal_first, dgGluingCompositionInputDiagonal_diagonal]
  apply dgGluingTriangleBoundaryFamily_hom_ext
  · rw [← Category.assoc, ← comp_whiskerRight, Subcomplex.homOfLE_ι]
    change ((horn 2 1).ι ▷ compositionCorrespondence x g) ≫
      compositionCorrespondenceEvaluation x g = _
    rw [compositionCorrespondenceEvaluation_horn, dgGluingCompositionInputBoundaryFamily_horn]
  · rw [← Category.assoc, ← comp_whiskerRight, boundary.ι_ι]
    change (stdSimplex.δ (1 : Fin 3) ▷ compositionCorrespondence x g) ≫
      compositionCorrespondenceEvaluation x g = _
    rw [dgGluingCompositionInputBoundaryFamily_diagonal,
      compositionCorrespondenceDiagonal_uncurry]

end SerrePositivity.InfinityCategories
