module

public import SerrePositivity.InfinityCategories.F2.EdgewiseRefinementEdges
public import SerrePositivity.InfinityCategories.F2.EdgewiseRefinementConstantProjections

/-!
概要：共通解像の二辺の宇宙持ち上げ後も元の精密化と二つの定値射影を保持する。
方針：実一単体の四射影の式を同じ ULift で写す。
規約：自然性に使用した同じ実辺全体を比較する。
使われ方：左右区間比較の二正方形を元の精密化の辺の類へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 自然性に使う右解像の右射影の実辺は元の精密化の同じ持ち上げ。 -/
lemma edgewiseRefinementRightEdgeUlift_right {X : SSet.{u}} (e : X _⦋1⦌) :
    ((edgewiseRefinementRightEdgeUlift.{u, v} e).map
      ((SSet.uliftFunctor.{v, u}).map (edgewiseRight X))).edge = ULift.up e :=
  congrArg ULift.up (edgewiseRefinementRightResolution_right e)

/-- 自然性に使う左解像の左射影の実辺は元の反転精密化の同じ持ち上げ。 -/
lemma edgewiseRefinementLeftEdgeUlift_left {X : SSet.{u}} (e : X _⦋1⦌) :
    ((edgewiseRefinementLeftEdgeUlift.{u, v} e).map
      ((SSet.uliftFunctor.{v, u}).map (edgewiseLeft X))).edge =
      ULift.up (SSet.opObjEquiv.symm e) :=
  congrArg ULift.up (edgewiseRefinementLeftResolution_left e)

/-- 右解像の残りの射影は持ち上げ後も元の始点に定値。 -/
lemma edgewiseRefinementRightEdgeUlift_left {X : SSet.{u}} (e : X _⦋1⦌) :
    ((edgewiseRefinementRightEdgeUlift.{u, v} e).map
      ((SSet.uliftFunctor.{v, u}).map (edgewiseLeft X))).edge =
      ULift.up (SSet.opObjEquiv.symm (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e)) :=
  congrArg ULift.up (edgewiseRefinementRightResolution_left e)

/-- 左解像の残りの射影は持ち上げ後も元の終点に定値。 -/
lemma edgewiseRefinementLeftEdgeUlift_right {X : SSet.{u}} (e : X _⦋1⦌) :
    ((edgewiseRefinementLeftEdgeUlift.{u, v} e).map
      ((SSet.uliftFunctor.{v, u}).map (edgewiseRight X))).edge =
      ULift.up (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e) :=
  congrArg ULift.up (edgewiseRefinementLeftResolution_right e)

end SerrePositivity.InfinityCategories.F2
