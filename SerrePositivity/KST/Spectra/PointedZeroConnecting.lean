module

public import SerrePositivity.KST.Spectra.PointedConnectingRepresentatives
public import SerrePositivity.KST.Spectra.LoopZeroPenultimate

/-!
概要：標準基点での基本群から fiber の連結成分への連結写像。
方針：像の基点と fiberPoint で構成済みの連結写像を、恒等射の基点移送で標準化する。
規約：fiber の零次数は集合であり、群演算を入れない。
使われ方：Goerss–Jardine I §8。零 loop 成分を介した骨格の微分の基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 標準 fiber の連結成分を、既存の fiberPoint の連結成分へ移す。 -/
def pointedFiberZeroEquiv {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) [Fibration p.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (pointedFiber p).right 0 (pointedFiber p).basepoint ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p.right (p.right.app _ E.basepoint)) 0
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso 0 (Iso.refl _) (PointedSimplicialSet.basepoint_ofVertex _ _)

/-- 概要：標準基点での基本群から fiber の連結成分への連結写像。
方針：底の基点を像へ戻し、元の連結写像を適用して標準 fiber 基点へ戻す。
規約：出力は pointed set の基礎集合。
使われ方：Goerss–Jardine I §8。loop の零次数と連結射の比較。 -/
def pointedConnectingZero {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    [Fibration p.right] [KanComplex B.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right 0 B.basepoint →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (pointedFiber p).right 0 (pointedFiber p).basepoint := fun a ↦
  (pointedFiberZeroEquiv p).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p.right E.basepoint 0
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl B.right)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)).symm a))

/-- 基点を標準化した fiber の境界頂点は、元の境界頂点へ移る。 -/
lemma BoundaryLift.pointedFiberZeroEquiv_mk {E B : PointedSimplicialSet.{u}} {p : E ⟶ B}
    [Fibration p.right] {s : B.right.PtSimplex 1 (p.right.app _ E.basepoint)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p.right E.basepoint s) :
    pointedFiberZeroEquiv p (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary L)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 L.boundary := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 (𝟙 _) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary L)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
  congr 1

/-- 概要：標準の零次数連結写像は任意の相対ホーン充填の最後の頂点で計算できる。
方針：底と fiber の二つの基点移送を消し、既存の充填の選択独立性を使う。
規約：fiber の成分の等式。
使われ方：Goerss–Jardine I §8。零 loop 成分の標準の連結写像への接続。 -/
lemma pointedConnectingZero_boundaryLift {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    [Fibration p.right] [KanComplex B.right]
    {s : B.right.PtSimplex 1 (p.right.app _ E.basepoint)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p.right E.basepoint s) :
    pointedConnectingZero p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl B.right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (_root_.SerrePositivity.KST.Spectra.BoundaryLift.pointedBoundary L) := by
  apply (pointedFiberZeroEquiv p).injective
  dsimp only [pointedConnectingZero]
  rw [Equiv.apply_symm_apply, MulEquiv.symm_apply_apply, BoundaryLift.pointedFiberZeroEquiv_mk,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p.right E.basepoint L]

end
end SerrePositivity.KST.Spectra
