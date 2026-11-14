module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ArrowCompositionIsoNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.LaxPullbacks.LaxHomArrowInterval

/-! 元の実 lax Hom 比較を、augmentation 二辺の同じ合成対角引き戻しへ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

def dgGluingDerivedAugmentationEdge (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedModuleArrow R C D M X.left X.right (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)

def dgGluingLaxHomArrowCompositionComparison (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso (dgGluingDerivedAugmentationEdge R C D M X)
      (dgGluingDerivedAugmentationEdge R C D M Y)).inv

lemma dgGluingLaxHomArrowCompositionComparison_recover (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso (dgGluingDerivedAugmentationEdge R C D M X)
          (dgGluingDerivedAugmentationEdge R C D M Y)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y := by
  rw [dgGluingLaxHomArrowCompositionComparison, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma dgGluingLaxHomArrowCompositionComparison_first (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomFirstComposition (dgGluingDerivedAugmentationEdge R C D M X)
        (dgGluingDerivedAugmentationEdge R C D M Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y) := by
  rw [dgGluingLaxHomArrowCompositionComparison, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso_inv_first
    (dgGluingDerivedAugmentationEdge R C D M X) (dgGluingDerivedAugmentationEdge R C D M Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y)

lemma dgGluingLaxHomArrowCompositionComparison_last (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomLastComposition (dgGluingDerivedAugmentationEdge R C D M X)
        (dgGluingDerivedAugmentationEdge R C D M Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y) := by
  rw [dgGluingLaxHomArrowCompositionComparison, Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso_inv_last
    (dgGluingDerivedAugmentationEdge R C D M X) (dgGluingDerivedAugmentationEdge R C D M Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
