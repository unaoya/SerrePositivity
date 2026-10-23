module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationComparisonBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaTargetBaseChange

/-!
概要：twisted arrow 全体の同じ復元射を、実際の Yoneda 対象前層の unstraightening へ制限する。
方針：全体の復元射の底変換と、小さい unstraightening の厳密な pullback 同型を合成する。
規約：対象ごとに別の図式同型から比較を選び直さず、全体の復元射を固定する。
使われ方：同じ恒等点と、第二変数の全 Hom パラメーターの輸送の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

/-- 同じ前層の unstraightening は、twisted arrow 全体の分類図式の終点固定の引き戻し。 -/
def twistedArrowTargetUnstraighteningIso {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    smallLeftUnstraightening (representablePresheafInfinity y) ≅
      pullback (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
        (twistedArrowTargetInclusion y) :=
  (smallLeftUnstraighteningMap_isPullback (representablePresheafInfinity y)
    (twistedArrowHomInfinity C) (twistedArrowTargetInclusion y)
    (representablePresheafInfinity_eq_targetRestriction y).symm).isoPullback

/-- 引き戻し同型の逆は、元の反転した底への射影を厳密に保つ。 -/
lemma twistedArrowTargetUnstraighteningIso_inv_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (twistedArrowTargetUnstraighteningIso y).inv ≫
      smallLeftUnstraighteningProjection (representablePresheafInfinity y) =
    pullback.snd (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
      (twistedArrowTargetInclusion y) :=
  (smallLeftUnstraighteningMap_isPullback (representablePresheafInfinity y)
    (twistedArrowHomInfinity C) (twistedArrowTargetInclusion y)
    (representablePresheafInfinity_eq_targetRestriction y).symm).isoPullback_inv_snd

/-- 全体への比較も、元の unstraightening の底変換写像そのものを回収する。 -/
lemma twistedArrowTargetUnstraighteningIso_inv_map
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (twistedArrowTargetUnstraighteningIso y).inv ≫
      smallLeftUnstraighteningMap (representablePresheafInfinity y) (twistedArrowHomInfinity C)
        (twistedArrowTargetInclusion y)
        (representablePresheafInfinity_eq_targetRestriction y).symm =
    pullback.fst (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
      (twistedArrowTargetInclusion y) :=
  (smallLeftUnstraighteningMap_isPullback (representablePresheafInfinity y)
    (twistedArrowHomInfinity C) (twistedArrowTargetInclusion y)
    (representablePresheafInfinity_eq_targetRestriction y).symm).isoPullback_inv_fst

/-- 同じ全体の復元射を終点固定で制限した、実際の前層の unstraightening への比較。 -/
def twistedArrowTargetReconstruction {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    twistedArrowTarget y ⟶ smallLeftUnstraightening (representablePresheafInfinity y) :=
  fiberComparisonBaseChange (twistedArrowProjection C)
      (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
      (leftStraighteningInfinityReconstruction (twistedArrowProjection C))
      (leftStraighteningInfinityReconstruction_projection (twistedArrowProjection C))
      (twistedArrowTargetInclusion y) ≫ (twistedArrowTargetUnstraighteningIso y).inv

/-- 制限した復元射は元の反転した底を厳密に保つ。 -/
lemma twistedArrowTargetReconstruction_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    twistedArrowTargetReconstruction y ≫
      smallLeftUnstraighteningProjection (representablePresheafInfinity y) =
    twistedArrowTargetProjection y := by
  rw [twistedArrowTargetReconstruction, Category.assoc,
    twistedArrowTargetUnstraighteningIso_inv_projection, fiberComparisonBaseChange_projection]
  rfl

/-- 制限した復元射を全体へ戻すと、元の全体の復元射を厳密に回収する。 -/
lemma twistedArrowTargetReconstruction_map
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    twistedArrowTargetReconstruction y ≫
      smallLeftUnstraighteningMap (representablePresheafInfinity y) (twistedArrowHomInfinity C)
        (twistedArrowTargetInclusion y)
        (representablePresheafInfinity_eq_targetRestriction y).symm =
    pullback.fst (twistedArrowProjection C) (twistedArrowTargetInclusion y) ≫
      leftStraighteningInfinityReconstruction (twistedArrowProjection C) := by
  rw [twistedArrowTargetReconstruction, Category.assoc,
    twistedArrowTargetUnstraighteningIso_inv_map, fiberComparisonBaseChange, pullback.lift_fst]

/-- 同じ全体の復元射の制限も、全空間の前合成同値。 -/
lemma twistedArrowTargetReconstruction_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsPrecompositionEquivalence (twistedArrowTargetReconstruction y) :=
  (fiberComparisonBaseChange_isPrecompositionEquivalence (twistedArrowProjection C)
    (smallLeftUnstraighteningProjection (twistedArrowHomInfinity C))
    (leftStraighteningInfinityReconstruction (twistedArrowProjection C))
    (leftStraighteningInfinityReconstruction_projection (twistedArrowProjection C))
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence (twistedArrowProjection C))
    (twistedArrowTargetInclusion y)).comp
      (isPrecompositionEquivalence_of_iso (twistedArrowTargetUnstraighteningIso y).symm)

end SerrePositivity.InfinityCategories
