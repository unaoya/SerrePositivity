module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeColumnHom
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDerivedRoof

/-!
# 相対表示の全屋根を元の通常導来屋根へ戻す

DAG XIII §2.2 の native な降下の補助。同じ全添字・指定 augmentation の逆・評価を
保持する。実 pinched 族との接続にはこの全 Arrow の等式を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.EInfinity.FrameHom SerrePositivity.EInfinity.SimplicialLocalization
open _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories (derivedInfinityCategory)
variable (A : Type u) [CommRing A] (X Y : Complex A)

/-- 相対表示の augmentation の順射は、元の通常導来 augmentation の全制限。 -/
lemma complexRelativeElementDerivedAugmentation_arrow :
    let I := normalizedTensorElementIndex A X Y
    let T := (hoFunctor.map ((pre (MixedNerve.down I)).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
    Arrow.mk (complexRelativeElementDerivedAugmentationIso A X Y).hom =
      Arrow.mk (T.map (normalizedTensorElementDerivedAugmentationIso A X Y).hom) := by
  have h₁ := congrArg Arrow.mk
    (NerveColumn.augmentationIso_hom (complexRelativeDerivedSource A)
      (complexRelativeElementColumn A X Y) (complexRelativeElementAugmentation A X Y)
      (complexRelativeElementDerivedAugmentation_invertible A X Y))
  exact h₁.trans
    (complexRelativeColumnHom_arrow A (normalizedTensorElementAugmentation A X Y))

/-- 同じ全屋根の逆左脚と評価の合成は、元の通常導来屋根の全制限である。 -/
lemma complexRelativeElementDerivedRoof_arrow :
    let I := normalizedTensorElementIndex A X Y
    let T := (hoFunctor.map ((pre (MixedNerve.down I)).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
    Arrow.mk ((complexRelativeElementDerivedAugmentationIso A X Y).inv ≫
      NerveColumn.hom (complexRelativeDerivedSource A) (complexRelativeElementEvaluation A X Y)) =
      Arrow.mk (T.map (normalizedTensorElementDerivedRoof A X Y)) := by
  let I := normalizedTensorElementIndex A X Y
  let T := (hoFunctor.map ((pre (MixedNerve.down I)).app
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
  have hp := complexRelativeElementDerivedAugmentation_arrow A X Y
  have hi : Arrow.mk (complexRelativeElementDerivedAugmentationIso A X Y).inv =
      Arrow.mk (T.map (normalizedTensorElementDerivedAugmentationIso A X Y).inv) := by
    simpa only [← Functor.map_inv, IsIso.Iso.inv_hom] using
      RoofPrefix.inv_arrow_eq _ _ hp
  have hs := complexRelativeColumnHom_arrow A (normalizedTensorElementEvaluation A X Y)
  change Arrow.mk (_ ≫ _) = Arrow.mk (T.map (_ ≫ _))
  rw [Functor.map_comp]
  exact RoofPrefix.comp_arrow_eq _ _ _ _ hi hs

end SerrePositivity.EInfinity.PowerOperation
