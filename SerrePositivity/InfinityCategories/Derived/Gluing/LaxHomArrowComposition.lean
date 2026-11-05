module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowCompositionIsoNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowInterval

/-! 元の実 lax Hom 比較を、augmentation 二辺の同じ合成対角引き戻しへ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedAugmentationEdge (X : DGGluingObject R C D M) :=
  dgGluingDerivedModuleArrow R C D M X.left X.right (dgGluingAugmentation R C D M X)

def dgGluingLaxHomArrowCompositionComparison (X Y : DGGluingObject R C D M) :=
  dgGluingLaxHomArrowIntervalComparison R C D M X Y ≫
    (dgGluingArrowCompositionIso (dgGluingDerivedAugmentationEdge R C D M X)
      (dgGluingDerivedAugmentationEdge R C D M Y)).inv

lemma dgGluingLaxHomArrowCompositionComparison_recover (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫
        (dgGluingArrowCompositionIso (dgGluingDerivedAugmentationEdge R C D M X)
          (dgGluingDerivedAugmentationEdge R C D M Y)).hom =
      dgGluingLaxHomArrowIntervalComparison R C D M X Y := by
  rw [dgGluingLaxHomArrowCompositionComparison, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma dgGluingLaxHomArrowCompositionComparison_first (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingArrowHomFirstComposition (dgGluingDerivedAugmentationEdge R C D M X)
        (dgGluingDerivedAugmentationEdge R C D M Y)
        (dgGluingLaxHomArrowIntervalComparison R C D M X Y) := by
  rw [dgGluingLaxHomArrowCompositionComparison, Category.assoc]
  exact dgGluingArrowCompositionIso_inv_first
    (dgGluingDerivedAugmentationEdge R C D M X) (dgGluingDerivedAugmentationEdge R C D M Y)
    (dgGluingLaxHomArrowIntervalComparison R C D M X Y)

lemma dgGluingLaxHomArrowCompositionComparison_last (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomArrowCompositionComparison R C D M X Y ≫ pullback.snd _ _ =
      dgGluingArrowHomLastComposition (dgGluingDerivedAugmentationEdge R C D M X)
        (dgGluingDerivedAugmentationEdge R C D M Y)
        (dgGluingLaxHomArrowIntervalComparison R C D M X Y) := by
  rw [dgGluingLaxHomArrowCompositionComparison, Category.assoc]
  exact dgGluingArrowCompositionIso_inv_last
    (dgGluingDerivedAugmentationEdge R C D M X) (dgGluingDerivedAugmentationEdge R C D M Y)
    (dgGluingLaxHomArrowIntervalComparison R C D M X Y)

end SerrePositivity.InfinityCategories
