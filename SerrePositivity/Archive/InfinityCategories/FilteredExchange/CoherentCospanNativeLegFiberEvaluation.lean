module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleSourceFiberEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeFaceSections

/-!
概要：native 錐の両辺上の切断を、端点を明示して元の二つの小さい fiber へ戻す。
方針：元の全三角形の表示等式と始点評価の同値を左右に適用する。
規約：両端の頂点等式を明示。使われ方：全三角形比較の実際の二脚への移送。
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
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection X) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection Y) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- native 左三角形の全図式は元の指定全三角形の一点評価そのもの。 -/
lemma coherentCospanNativeLeftTriangleDiagram_eq :
    Dl = coherentTransformationPointDiagram C.leftTriangle.diagram (ULift.up b) := by
  rw [coherentCospanConePointwiseCone_leftTriangle, coherentTransformationPointTriangle,
    Equiv.symm_apply_apply]

/-- native 右三角形の全図式も元の指定全三角形の一点評価そのもの。 -/
lemma coherentCospanNativeRightTriangleDiagram_eq :
    Dr = coherentTransformationPointDiagram C.rightTriangle.diagram (ULift.up b) := by
  rw [coherentCospanConePointwiseCone_rightTriangle, coherentTransformationPointTriangle,
    Equiv.symm_apply_apply]

/-- 左辺上の切断を、元の左の小さい fiber へ戻す同じ始点評価。 -/
def coherentCospanNativeLeftSourceFiberEvaluation :=
  coherentTriangleSourceFiberEvaluation F X Z C.toLeft C.fromLeft C.leftTriangle b Dl
    (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)

/-- 右辺上の切断を、元の右の小さい fiber へ戻す同じ始点評価。 -/
def coherentCospanNativeRightSourceFiberEvaluation :=
  coherentTriangleSourceFiberEvaluation F Y Z C.toRight C.fromRight C.rightTriangle b Dr
    (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)

/-- 左辺の始点評価の同値性は、元の頂点の同定から従う。 -/
lemma coherentCospanNativeLeftSourceFiberEvaluation_isQCatEquivalence :
    IsQCatEquivalence (coherentCospanNativeLeftSourceFiberEvaluation F X Y Z C b) :=
  coherentTriangleSourceFiberEvaluation_isQCatEquivalence F X Z C.toLeft C.fromLeft
    C.leftTriangle b Dl (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)

/-- 右辺でも同じ実際の始点評価は同値。 -/
lemma coherentCospanNativeRightSourceFiberEvaluation_isQCatEquivalence :
    IsQCatEquivalence (coherentCospanNativeRightSourceFiberEvaluation F X Y Z C b) :=
  coherentTriangleSourceFiberEvaluation_isQCatEquivalence F Y Z C.toRight C.fromRight
    C.rightTriangle b Dr (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
