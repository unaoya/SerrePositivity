module
public import SerrePositivity.InfinityCategories.Stable.LoopConeUniversalSelfComparison
public import SerrePositivity.InfinityCategories.Stable.LoopConeClassifierFiberEquivalence

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
def loopConeFixedApexSourceLift {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square) x ⟶
      vertexFiber (loopConeObjectSource X) x :=
  (loopConeFixedApexDiagramFiberIso t x).hom ≫
    vertexFiberι (loopConeSourceFiberProjection X x) t.diagramVertex

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeFixedApexSourceLift_ι {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    loopConeFixedApexSourceLift t x ≫ vertexFiberι (loopConeObjectSource X) x =
      loopConeFixedApexLift t x := by
  exact loopConeFixedApexDiagramFiberIso_lift t x

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeFixedApexSourceLift_classifier_h {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    (unitCommaFiberHomotopy
      (loopConeFixedApexSourceLift t x ≫ loopConeClassifierSourceFiberMap X x)).h =
      (loopConeFixedApexLift t x ▷ (Δ[1] : SSet.{u})) ≫
        (loopConeApexComparisonHomotopy X).h := by
  change (unitCommaHomotopy
    ((loopConeFixedApexSourceLift t x ≫ loopConeClassifierSourceFiberMap X x) ≫
      vertexFiberι (unitCommaSource (loopDiagramEvaluation X 0 0)) x)).h = _
  have hi : (loopConeFixedApexSourceLift t x ≫ loopConeClassifierSourceFiberMap X x) ≫
      vertexFiberι (unitCommaSource (loopDiagramEvaluation X 0 0)) x =
      loopConeFixedApexLift t x ≫ loopConeClassifier X := by
    rw [Category.assoc, loopConeClassifierSourceFiberMap_ι, ← Category.assoc,
      loopConeFixedApexSourceLift_ι]
  exact (congrArg (fun q : HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square) x ⟶
    unitComma (loopDiagramEvaluation X 0 0) ↦ (unitCommaHomotopy q).h) hi).trans (by
      rw [unitCommaHomotopy_precomp, loopConeClassifier, unitCommaHomotopy_lift_h])
end SerrePositivity.InfinityCategories
