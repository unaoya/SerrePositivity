module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakArrowRoundTripComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActionHomotopy

/-!
# 指定射の前後合成の両逆を与えるホモトピー

概要：元の指定射の前後合成と逆向き列の前後合成はホモトピー逆となる。
方針：往復の単位へのホモトピーを元の豊穣合成へ代入する。
規約：端点はそれぞれ元の対象を用い、Kan 性を要求しない。
使われ方：相対自然変換による hammock の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} (g : X ⟶ Y) (hg : W g)

def postSourceHomotopy (A : C) : SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W A X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap_comp]
  have H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposeHomotopy A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceCompositeHomotopy g hg)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap_unit] at H
  exact H

def postTargetHomotopy (A : C) : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W A Y)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap_comp]
  have H : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W Y)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposeHomotopy A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetCompositeHomotopy g hg)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap_unit] at H
  exact H

def preSourceHomotopy (A : C) : SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X A))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) A) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap_comp]
  have H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X) A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg)) A) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposeHomotopy A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceCompositeHomotopy g hg)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap_unit] at H
  exact H

def preTargetHomotopy (A : C) : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) A)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y A)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap_comp]
  have H : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap g hg) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g)) A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W Y) A) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposeHomotopy A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetCompositeHomotopy g hg)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap_unit] at H
  exact H

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
