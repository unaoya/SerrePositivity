module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallFiberTriangleEdgeSections
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLegFiberEvaluation

/-!
概要：元の二つの標的 fiber から、native cospan の同じ二辺の切断空間へ比較同値を作る。
方針：native 辺と元の指定変換の一点評価の厳密な等式で、普遍 prism の切断族を移す。
規約：元の二作用・図式辺を保持。使われ方：実 fiber cospan と切断 cospan の同値比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)

/-- native 左図式辺は、元の左から最後への指定変換の一点評価そのもの。 -/
lemma coherentCospanNativeLeftDiagramEdge_eq_point :
    horn₂₂.ι₀₂ ≫ d = coherentTransformationPointEdge X Z C.fromLeft b := by
  have h := nativeConeTriangle_diagram_edge c el
  have hd : stdSimplex.δ (0 : Fin 3) ≫ Dl = horn₂₂.ι₀₂ ≫ d := by
    simpa only [Equiv.symm_apply_apply, coherentCospanConePointwiseCone] using h
  exact hd.symm.trans ((congrArg (fun k => stdSimplex.δ (0 : Fin 3) ≫ k)
    (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)).trans
      (coherentTransformationPointDiagram_second C.leftTriangle (ULift.up b)))

/-- native 右図式辺も、元の右から最後への指定変換の一点評価そのもの。 -/
lemma coherentCospanNativeRightDiagramEdge_eq_point :
    horn₂₂.ι₁₂ ≫ d = coherentTransformationPointEdge Y Z C.fromRight b := by
  have h := nativeConeTriangle_diagram_edge c er
  have hd : stdSimplex.δ (0 : Fin 3) ≫ Dr = horn₂₂.ι₁₂ ≫ d := by
    simpa only [Equiv.symm_apply_apply, coherentCospanConePointwiseCone] using h
  exact hd.symm.trans ((congrArg (fun k => stdSimplex.δ (0 : Fin 3) ≫ k)
    (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)).trans
      (coherentTransformationPointDiagram_second C.rightTriangle (ULift.up b)))

/-- 元の左の小さい fiber から、同じ native 左辺上の切断への比較同値。 -/
def coherentCospanNativeLeftFiberEdgeSections : coherentNativeTriangleFiberParameters X b ⟶
    relativeFunctorSpace pointedSpaceProjection (horn₂₂.ι₀₂ ≫ d) :=
  coherentSmallFiberEdgeSectionsOfEq X Z C.fromLeft b (horn₂₂.ι₀₂ ≫ d)
    (coherentCospanNativeLeftDiagramEdge_eq_point F X Y Z C b)

/-- 元の右の小さい fiber から、同じ native 右辺上の切断への比較同値。 -/
def coherentCospanNativeRightFiberEdgeSections : coherentNativeTriangleFiberParameters Y b ⟶
    relativeFunctorSpace pointedSpaceProjection (horn₂₂.ι₁₂ ≫ d) :=
  coherentSmallFiberEdgeSectionsOfEq Y Z C.fromRight b (horn₂₂.ι₁₂ ≫ d)
    (coherentCospanNativeRightDiagramEdge_eq_point F X Y Z C b)

/-- 左の fiber から元の左辺の切断空間への比較は同値。 -/
lemma coherentCospanNativeLeftFiberEdgeSections_isQCatEquivalence :
    IsQCatEquivalence (coherentCospanNativeLeftFiberEdgeSections F X Y Z C b) :=
  coherentSmallFiberEdgeSectionsOfEq_isQCatEquivalence X Z C.fromLeft b _ _

/-- 右の fiber から元の右辺の切断空間への比較も同値。 -/
lemma coherentCospanNativeRightFiberEdgeSections_isQCatEquivalence :
    IsQCatEquivalence (coherentCospanNativeRightFiberEdgeSections F X Y Z C b) :=
  coherentSmallFiberEdgeSectionsOfEq_isQCatEquivalence Y Z C.fromRight b _ _

local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection X) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection Y) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 左の実 fiber と元の辺の切断空間は、この具体的な比較射で単体的ホモトピー同値。 -/
lemma coherentCospanNativeLeftFiberEdgeSections_isSimplicialHomotopyEquivalence :
    IsSimplicialHomotopyEquivalence (coherentCospanNativeLeftFiberEdgeSections F X Y Z C b) := by
  have h := coherentCospanNativeLeftFiberEdgeSections_isQCatEquivalence F X Y Z C b
  exact h.isSimplicialHomotopyEquivalence

/-- 右も元の実際の比較射による単体的ホモトピー同値である。 -/
lemma coherentCospanNativeRightFiberEdgeSections_isSimplicialHomotopyEquivalence :
    IsSimplicialHomotopyEquivalence (coherentCospanNativeRightFiberEdgeSections F X Y Z C b) := by
  have h := coherentCospanNativeRightFiberEdgeSections_isQCatEquivalence F X Y Z C b
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
