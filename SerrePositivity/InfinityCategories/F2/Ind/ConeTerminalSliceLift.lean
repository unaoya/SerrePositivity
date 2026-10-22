module

public import SerrePositivity.InfinityCategories.F2.Ind.JoinAssociatorOuterPair
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationTipTriangle
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：指定頂点への全余錐を、恒等射で終わる同じ頂点の slice へ持ち上げる。
方針：二重余錐の右二点を折り畳んで curry する。
規約：元の全余錐と底側の全図式を厳密に保持。使われ方：補間の持ち上げ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} (x : X _⦋0⦌) (b : join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)

/-- 同じ全余錐を被覆し、恒等射で終わる終点 slice 内の標準持ち上げ。 -/
def coneTerminalSliceLift : join A (Δ[0] : SSet.{u}) ⟶
    sliceOver (SSet.yonedaEquiv.symm x) :=
  sliceOverCurry (arrowInterpolationConeFold A ≫ b) (by
    rw [← Category.assoc, arrowInterpolationConeFold_inr, hb])

/-- 標準持ち上げは、元の全余錐そのものを被覆する。 -/
lemma coneTerminalSliceLift_projection :
    coneTerminalSliceLift x b hb ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b := by
  rw [coneTerminalSliceLift, sliceOverCurry_projection, ← Category.assoc,
    arrowInterpolationConeFold_inl, Category.id_comp]

/-- 底上の制限は、元の全余錐をそのまま curry した族。 -/
lemma coneTerminalSliceLift_old :
    joinInl A (Δ[0] : SSet.{u}) ≫ coneTerminalSliceLift x b hb = sliceOverCurry b hb := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm x)
  rw [sliceOverUncurry_precomp, coneTerminalSliceLift, sliceOverUncurry_curry,
    sliceOverUncurry_curry, ← Category.assoc, arrowInterpolationConeFold_outerPair,
    Category.id_comp]

/-- 標準持ち上げの終点は、同じ指定頂点の恒等射そのもの。 -/
lemma coneTerminalSliceLift_tip :
    joinInr A (Δ[0] : SSet.{u}) ≫ coneTerminalSliceLift x b hb =
      SSet.yonedaEquiv.symm (sliceIdentityCone x) := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm x)
  rw [sliceOverUncurry_precomp, coneTerminalSliceLift, sliceOverUncurry_curry,
    sliceOverUncurry_yoneda, ← Category.assoc, arrowInterpolationConeFold_rightPair,
    Category.assoc]
  change stableLastJoinEvaluation 0 ≫ (joinInr A Δ[0] ≫ b) = SSet.const x
  rw [hb, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2.Ind
