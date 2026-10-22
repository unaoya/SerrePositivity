module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeFoldNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.JoinAssociatorOuterPair
public import SerrePositivity.InfinityCategories.F2.Ind.IntervalTerminalSliceSection

/-!
概要：同じ指定点写像の標準 slice 持ち上げは、指定された全終端辺も保持する。
方針：右二点の折り畳みの自然性と区間表示を使う。
規約：元の点写像の slice 内で比較。使われ方：区間 D 全体を固定した持ち上げ同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の指定点写像への全余錐の、同じ点の slice 内の標準持ち上げ。 -/
def conePointSliceLift {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p) :
    join A (Δ[0] : SSet.{u}) ⟶ sliceOver p :=
  sliceOverCurry (arrowInterpolationConeFold A ≫ b) (by
    rw [← Category.assoc, arrowInterpolationConeFold_inr, hb])

/-- 標準持ち上げは、同じ元の全余錐を被覆する。 -/
lemma conePointSliceLift_projection {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p) :
    conePointSliceLift p b hb ≫ sliceOverProjection p = b := by
  rw [conePointSliceLift, sliceOverCurry_projection, ← Category.assoc,
    arrowInterpolationConeFold_inl, Category.id_comp]

/-- 底の制限は、元の全余錐を curry した同じ族。 -/
lemma conePointSliceLift_old {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p) :
    joinInl A (Δ[0] : SSet.{u}) ≫ conePointSliceLift p b hb = sliceOverCurry b hb := by
  apply sliceOverUncurry_injective p
  rw [sliceOverUncurry_precomp, conePointSliceLift, sliceOverUncurry_curry,
    sliceOverUncurry_curry, ← Category.assoc, arrowInterpolationConeFold_outerPair,
    Category.id_comp]

/-- 指定された元の全終端辺は、同じ区間の標準 slice 切断として厳密に回収。 -/
lemma conePointSliceLift_edge {A X : SSet.{u}} (d : (Δ[1] : SSet.{u}) ⟶ X)
    (b : join A (Δ[0] : SSet.{u}) ⟶ X)
    (hb : joinInr A Δ[0] ≫ b = stdSimplex.δ 0 ≫ d) (a : (Δ[0] : SSet.{u}) ⟶ A)
    (ha : joinMap a (𝟙 Δ[0]) ≫ b = (joinStdSimplexIso 0 0).hom ≫ d) :
    joinMap a (𝟙 Δ[0]) ≫ conePointSliceLift (stdSimplex.δ 0 ≫ d) b hb =
      (joinStdSimplexIso 0 0).hom ≫ intervalTerminalSliceSection d := by
  apply sliceOverUncurry_injective (stdSimplex.δ 0 ≫ d)
  rw [sliceOverUncurry_precomp, conePointSliceLift, sliceOverUncurry_curry,
    sliceOverUncurry_precomp, intervalTerminalSliceSection, sliceOverUncurry_curry,
    ← Category.assoc, arrowInterpolationConeFold_naturality, Category.assoc, ha,
    ← Category.assoc, arrowInterpolationConeFold_interval, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
