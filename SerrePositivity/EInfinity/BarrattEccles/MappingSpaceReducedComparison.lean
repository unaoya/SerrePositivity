module

public import SerrePositivity.EInfinity.BarrattEccles.ReducedHammockWeakComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakAnodyneLocalization

/-!
# 元の Map^h と同じ reduced hammock の高次比較

概要：同じ元の反対要素圏の nerve からの両弱同値でホモトピー型を比較する。
方針：実際の左 augmentation と右 hammock 射を anodyne 局所化で反転する。
規約：元の全単体と同じ二射への回収式を保持する。
使われ方：実 DK Hom との比較の共通標的。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)
def mappingSpaceReducedHammockComparisonIso :
    AnodyneHomotopy.anodyneQ.obj
        (SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y)) ≅
      AnodyneHomotopy.anodyneQ.obj (algebraReducedHammock A X Y) := by
  have := mappingSpaceIndexAugmentation_localized_isIso A X Y
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak (mappingSpaceReducedHammockNerveMap A X Y)
    (mappingSpaceReducedHammockNerveMap_isWeakHomotopyEquivalence A X Y)
  exact (asIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y))).symm ≪≫
    asIso (AnodyneHomotopy.anodyneQ.map (mappingSpaceReducedHammockNerveMap A X Y))
lemma mappingSpaceReducedHammockComparisonIso_fac :
    AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceReducedHammockComparisonIso A X Y).hom =
      AnodyneHomotopy.anodyneQ.map (mappingSpaceReducedHammockNerveMap A X Y) := by
  have := mappingSpaceIndexAugmentation_localized_isIso A X Y
  change AnodyneHomotopy.anodyneQ.map _ ≫ (inv (AnodyneHomotopy.anodyneQ.map _) ≫ _) = _
  exact IsIso.hom_inv_id_assoc _ _
end SerrePositivity.EInfinity.BarrattEccles
