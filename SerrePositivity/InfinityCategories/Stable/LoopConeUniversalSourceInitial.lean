module
public import SerrePositivity.InfinityCategories.Stable.LoopConeFixedApexSourceLift
public import SerrePositivity.InfinityCategories.Stable.LoopCommaInitialArrow

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
lemma loopConeUniversalSourcePoint_isInitial {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    {y : X _⦋0⦌} (t : LoopSquare y) :
    let x := (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square))
    IsInitialVertex ((loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌)
      (loopConeUniversalFixedApexPoint t)) := by
  let p := pullbackCospan t.square
  let c := (sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (pullbackCone t.square)
  let x := (HomotopyLimits.coneFamilyApex p).app (Opposite.op ⦋0⦌) c
  let v := loopConeUniversalFixedApexPoint t
  let L := loopConeFixedApexLift t x
  let f := loopConeFixedApexSourceLift t x ≫ loopConeClassifierSourceFiberMap X x
  have hh := loopConeFixedApexSourceLift_classifier_h t x
  have hid : L.app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj
        (HomotopyLimits.fixedApexConeFamily p x)) v).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (loopConeObjects X))
        (L.app (Opposite.op ⦋0⦌) v)).edge :=
    ConcreteCategory.congr_hom (L.naturality (SimplexCategory.σ (0 : Fin 1)).op) v
  have hraw := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj
      (HomotopyLimits.fixedApexConeFamily p x)) v).edge, homotopyIntervalEdge.edge)) hh
  change (unitCommaFiberHomotopy f).h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj
        (HomotopyLimits.fixedApexConeFamily p x)) v).edge, homotopyIntervalEdge.edge) =
    (loopConeApexComparisonHomotopy X).h.app (Opposite.op ⦋1⦌)
      (L.app (Opposite.op ⦋1⦌)
        (SSet.Truncated.Edge.id (X := (truncation 2).obj
          (HomotopyLimits.fixedApexConeFamily p x)) v).edge, homotopyIntervalEdge.edge) at hraw
  rw [hid] at hraw
  have he : IsInvertibleEdge
      (simplicialHomotopyVertexEdge (unitCommaFiberHomotopy f) v).toTruncated :=
    (isInvertibleEdge_congr hraw).mpr (loopConeUniversalApexComparison_isInvertible t)
  have ha := unitCommaFiberArrowHom_isIso_of_family_vertexEdge f v he
  have hi := (loopUnitCommaFiber_isInitial_iff_invertibleArrow s hs hΩ x
    (f.app (Opposite.op ⦋0⦌) v)).mpr ha
  let e := (loopConeClassifierSourceFiberMap_isQCatEquivalence X x).choose
  exact (e.isInitialVertex_iff
    ((loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌) v)).mpr hi
end SerrePositivity.InfinityCategories
