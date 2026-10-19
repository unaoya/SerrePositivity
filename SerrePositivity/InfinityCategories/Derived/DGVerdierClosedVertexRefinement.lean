module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierVertexLegTriangle
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdgeCompositionEquality
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofRefinements

/-! # 頂点錐の辺族に依存しない一つの閉始点細分

概要：元の頂点錐と一つの追加実閉分母だけから、共通閉細分分母と実 apex を固定する。
方針：閉分母の合成表示を保持する。使われ方：高次の全辺錐に共通な頂点脚の構成。
規約：辺族や各充填の選択をデータに含めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f)

/-- 頂点錐の同じ追加実閉分母。辺の族や充填の選択に依存しない。 -/
structure DGVerdierClosedVertexRefinement where
  q : D
  s : ForgetEnrichment.of (Complex A) q ⟶ C.denominator.obj.left
  denominator : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P

variable (R : DGVerdierClosedVertexRefinement A D C)

/-- 元の共通閉分母を同じ追加閉分母で細分した、一つの閉実分母。 -/
def DGVerdierClosedVertexRefinement.commonDenominator : DGClosedVerdierDenominators A D P x :=
  dgClosedRoofRefine A D P x C.denominator R.s R.denominator

/-- 全辺に共通する、同じ閉細分分母の実 over 頂点。 -/
def DGVerdierClosedVertexRefinement.commonApex : (dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  dgClosedVerdierDenominatorVertex A D P x R.commonDenominator

end SerrePositivity.InfinityCategories
