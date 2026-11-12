module
public import SerrePositivity.KST.SConstruction.KZeroGroupoidPresentation
public import SerrePositivity.KST.SConstruction.ObjectRawBoundaryEdges
public import SerrePositivity.KST.SConstruction.ObjectKClassTriangle

/-! # 基本亜群の表示における元の対象 K 類
概要：実際の BF 零次群の対象類を、置換前の同じ object S₁ の辺の形式的な類で計算する。
方針：元の辺の Kan 単位での回収と、基本群での既存の逆元の式を表示同値へ渡す。
規約：元の loop の逆元の向きを保持する。使われ方：三角圏 K₀ 比較の逆写像の対象類。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の object S₁ の辺を元の境界商の基本亜群の自己射とする。 -/
def objectBoundaryPath (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    boundaryFundamentalBasepoint X ⟶ boundaryFundamentalBasepoint X :=
  FreeGroupoid.homMk (SSet.Truncated.HomotopyCategory.homMk
    (fundamentalLoopEdge (objectRawBoundaryEdge X e)))

/-- 元の対象の実際の K 類は、元の object S₁ の同じ辺の形式的な類の逆で表示される。 -/
lemma kZeroGroupoidPresentation_objectKClass (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    kZeroGroupoidPresentation X
      (Additive.toMul (objectKClass X ((sOneComparison X.carrier).app _ e))) =
        inv (objectBoundaryPath X e) := by
  let p : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (((boundaryKanRealizationFunctor 0).obj X).right) 0
      ((boundaryKanRealizationFunctor 0).obj X).basepoint ≃
        (boundaryFundamentalBasepoint X ⟶ boundaryFundamentalBasepoint X) :=
    kanAnodyneLoopPresentation (B := ((boundaryKanRealizationFunctor 0).obj X).right)
      (PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right
      (PointedKanReplacement.unit_anodyne (boundaryReducedRealization 0 X))
      (boundaryReducedRealization 0 X).basepoint
  have hp := kanAnodyneLoopPresentation_mk
    (B := ((boundaryKanRealizationFunctor 0).obj X).right)
    (PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right
    (PointedKanReplacement.unit_anodyne (boundaryReducedRealization 0 X))
    (boundaryReducedRealization 0 X).basepoint (objectRawBoundaryEdge X e)
  have hc : p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X e)) = objectBoundaryPath X e :=
    (congrArg (fun s => p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) (objectRawBoundaryEdge_kan X e)).symm.trans hp
  have hi : p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X e))⁻¹ =
      inv (p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (objectBoundaryEdge X e))) :=
    kanAnodyneLoopPresentation_inv _ _ _ _
  exact (congrArg p (objectBoundaryEdge_objectKClass X e)).trans
    (hi.trans (congrArg (fun a => inv a) hc))

end SerrePositivity.KST.SConstruction
