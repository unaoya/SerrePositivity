module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WeakArrowRoundTripComposition
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.PointActionHomotopy

/-!
# 指定射の前後合成の両逆を与えるホモトピー

概要：元の指定射の前後合成と逆向き列の前後合成はホモトピー逆となる。
方針：往復の単位へのホモトピーを元の豊穣合成へ代入する。
規約：端点はそれぞれ元の対象を用い、Kan 性を要求しない。
使われ方：相対自然変換による hammock の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WeakArrow
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y : C} (g : X ⟶ Y) (hg : W g)

def postSourceHomotopy (A : C) : SSet.Homotopy (𝟙 (colimitGraph W A X))
    (postcomposePointMap A (arrowMap W g) ≫ postcomposePointMap A (backwardMap g hg)) := by
  rw [postcomposePointMap_comp]
  have H : SSet.Homotopy (postcomposePointMap A (colimitUnit W X))
      (postcomposePointMap A (composeUnitMaps (arrowMap W g) (backwardMap g hg))) :=
    postcomposeHomotopy A (sourceCompositeHomotopy g hg)
  rw [postcomposePointMap_unit] at H
  exact H

def postTargetHomotopy (A : C) : SSet.Homotopy
    (postcomposePointMap A (backwardMap g hg) ≫ postcomposePointMap A (arrowMap W g))
      (𝟙 (colimitGraph W A Y)) := by
  rw [postcomposePointMap_comp]
  have H : SSet.Homotopy
      (postcomposePointMap A (composeUnitMaps (backwardMap g hg) (arrowMap W g)))
      (postcomposePointMap A (colimitUnit W Y)) :=
    postcomposeHomotopy A (targetCompositeHomotopy g hg)
  rw [postcomposePointMap_unit] at H
  exact H

def preSourceHomotopy (A : C) : SSet.Homotopy (𝟙 (colimitGraph W X A))
    (precomposePointMap (backwardMap g hg) A ≫ precomposePointMap (arrowMap W g) A) := by
  rw [precomposePointMap_comp]
  have H : SSet.Homotopy (precomposePointMap (colimitUnit W X) A)
      (precomposePointMap (composeUnitMaps (arrowMap W g) (backwardMap g hg)) A) :=
    precomposeHomotopy A (sourceCompositeHomotopy g hg)
  rw [precomposePointMap_unit] at H
  exact H

def preTargetHomotopy (A : C) : SSet.Homotopy
    (precomposePointMap (arrowMap W g) A ≫ precomposePointMap (backwardMap g hg) A)
      (𝟙 (colimitGraph W Y A)) := by
  rw [precomposePointMap_comp]
  have H : SSet.Homotopy
      (precomposePointMap (composeUnitMaps (backwardMap g hg) (arrowMap W g)) A)
      (precomposePointMap (colimitUnit W Y) A) :=
    precomposeHomotopy A (targetCompositeHomotopy g hg)
  rw [precomposePointMap_unit] at H
  exact H

end SerrePositivity.EInfinity.Hammock.WeakArrow
