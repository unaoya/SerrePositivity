module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceLift
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationTipTriangle
public import SerrePositivity.InfinityCategories.F2.Ind.PointSliceIdentityProjection

/-!
概要：任意の元の点写像への標準 slice 持ち上げは、同じ点の恒等錐で終わる。
方針：元の二重余錐の右二点の折り畳みを、同じ全底余錐へ合成する。
規約：元の点写像と全底余錐を保持する。
使われ方：任意の元の点の比較を、同じ right-anodyne 制限の指定逆像で直接構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の点への標準持ち上げの終端の全錐は、同じ元の点の恒等錐。
方針：元の右二点の折り畳み。規約：全射の等号。使われ方：指定比較の元の終点条件。 -/
lemma conePointSliceLift_tip_uncurry {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p) :
    sliceOverUncurry (joinInr A Δ[0] ≫ conePointSliceLift p b hb) =
      SSet.const (SSet.yonedaEquiv p) := by
  rw [sliceOverUncurry_precomp, conePointSliceLift, sliceOverUncurry_curry,
    ← Category.assoc, arrowInterpolationConeFold_rightPair, Category.assoc, hb]
  have he : stableLastJoinEvaluation.{u} 0 =
      SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he, SSet.const_comp]
  rfl
end SerrePositivity.InfinityCategories.F2.Ind
