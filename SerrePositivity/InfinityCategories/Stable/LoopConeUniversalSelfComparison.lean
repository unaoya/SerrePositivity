module
public import SerrePositivity.InfinityCategories.Stable.LoopConeFixedApexDiagramFiber
public import SerrePositivity.InfinityCategories.Stable.LoopConeClassifierInterval
public import SerrePositivity.InfinityCategories.Stable.UnitCommaFamilyArrow

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
def loopConeUniversalFixedApexPoint {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) :
    (HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square)
      ((HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
        ((sliceConeFamilyMap (pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
          (pullbackCone t.square)))) _⦋0⦌ :=
  ⟨(sliceConeFamilyMap (pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
    (pullbackCone t.square), by rw [pinchedConstant_zero]⟩

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeUniversalComparison_isInvertible {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) :
    let x := (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square))
    IsInvertibleEdge (simplicialHomotopyVertexEdge (loopConeFixedApexComparison t x)
      (loopConeUniversalFixedApexPoint t)).toTruncated := by
  let c := (sliceConeFamilyMap (pullbackCospan t.square)).app
    (Opposite.op ⦋0⦌) (pullbackCone t.square)
  let x := (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app (Opposite.op ⦋0⦌) c
  let H := loopConeFixedApexComparison t x
  have hc : IsTerminalVertex c := by
    let e := (isQCatEquivalence_sliceConeFamilyMap (pullbackCospan t.square)).choose
    exact (e.isTerminalVertex_iff (pullbackCone t.square)).mp t.isPullback
  have hs : IsTerminalVertex
      ((vertexFiberι (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)) x).app
        (Opposite.op ⦋0⦌) (loopConeUniversalFixedApexPoint t)) := hc
  have ht : IsTerminalVertex
      ((SSet.const c : HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square) x ⟶
        coneFamily (pullbackCospan t.square)).app (Opposite.op ⦋0⦌)
          (loopConeUniversalFixedApexPoint t)) := by
    change IsTerminalVertex (PinchedHom.constant c 0)
    rw [pinchedConstant_zero]
    exact hc
  exact CategoryTheory.Limits.isIso_of_isTerminal hs.isTerminalHo ht.isTerminalHo _

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeUniversalApexComparison_isInvertible {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) :
    let x := (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square))
    IsInvertibleEdge (simplicialHomotopyVertexEdge (loopConeApexComparisonHomotopy X)
      ((loopConeFixedApexLift t x).app (Opposite.op ⦋0⦌)
        (loopConeUniversalFixedApexPoint t))).toTruncated := by
  let p := pullbackCospan t.square
  let q := HomotopyLimits.coneFamilyApex p
  let c := (sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (pullbackCone t.square)
  let x := q.app (Opposite.op ⦋0⦌) c
  let v := loopConeUniversalFixedApexPoint t
  let H := loopConeFixedApexComparison t x
  let L := loopConeFixedApexLift t x
  have he := (loopConeUniversalComparison_isInvertible t).map q
  have hh : H.h ≫ q = (L ▷ (Δ[1] : SSet.{u})) ≫
      (loopConeApexComparisonHomotopy X).h := by
    change H.h ≫ HomotopyLimits.coneFamilyApex p = _
    conv_lhs =>
      arg 2
      rw [coneFamilyApex_eq_vertexEvaluation]
    rw [← Category.assoc, loopConeFixedApexComparison_ι]
    exact Category.assoc _ _ _
  have hid : L.app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj
        (HomotopyLimits.fixedApexConeFamily p x)) v).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (loopConeObjects X))
        (L.app (Opposite.op ⦋0⦌) v)).edge :=
    ConcreteCategory.congr_hom (L.naturality (SimplexCategory.σ (0 : Fin 1)).op) v
  have hraw := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj
      (HomotopyLimits.fixedApexConeFamily p x)) v).edge, homotopyIntervalEdge.edge)) hh
  change q.app (Opposite.op ⦋1⦌)
      (H.h.app (Opposite.op ⦋1⦌)
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj
          (HomotopyLimits.fixedApexConeFamily p x)) v).edge, homotopyIntervalEdge.edge)) =
    (loopConeApexComparisonHomotopy X).h.app (Opposite.op ⦋1⦌)
      (L.app (Opposite.op ⦋1⦌)
        (SSet.Truncated.Edge.id (X := (truncation 2).obj
          (HomotopyLimits.fixedApexConeFamily p x)) v).edge, homotopyIntervalEdge.edge) at hraw
  rw [hid] at hraw
  exact (isInvertibleEdge_congr hraw).mp he
end SerrePositivity.InfinityCategories
