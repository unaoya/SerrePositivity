module

public import SerrePositivity.KST.Spectra.LoopConnectingStandardRepresentatives
public import SerrePositivity.KST.Spectra.LoopConnectingZeroFiber
public import SerrePositivity.KST.Spectra.PointedZeroConnecting

/-!
概要：零 loop 成分と標準の接続写像の反可換式。
方針：共通 path の境界代表を標準基点へ移し、商の任意の入力に移す。
規約：零 loop の成分は集合で扱い、fiber の基本群において逆元を取る。
使われ方：Goerss–Jardine I §8。骨格の微分の反復 loop 比較の基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.LoopConnectingComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)

/-- 概要：標準の連結準同型は、path の最後の面から得る loop の代表で反可換。
方針：両連結射を任意の充填の境界で計算し、共通の path の逆元公式を使う。
規約：標準の fiber 基点と既存 loop–fiber 同型を保持する。
使われ方：Goerss–Jardine I §8。商の任意の入力に移す前の代表での式。 -/
theorem pointedConnecting_zero_loop_representative [Fibration p.right]
    [KanComplex E.right] [KanComplex B.right]
    (t : B.right.PtSimplex 2 (p.right.app _ E.basepoint))
    (N : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (pathEndpoint B).right (basedPathSpace B).basepoint (pathBaseSimplex p t))
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p.right E.basepoint t)
    (V : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint (sourceLoop p t N)) :
    loopZeroHomotopyEquiv (pointedFiber p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 (loopPointedFiberIso p).inv.right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (loopPointedFiberIso p).inv)
        (pointedConnectingZero (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
            (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
              (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (sourceLoop p t N))))) =
      (pointedConnectingHom p 0
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 1 (Iso.refl B.right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t)))⁻¹ := by
  have : Fibration (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right := by
    infer_instance
  apply (pointedFiberGroupEquiv p 0).injective
  rw [map_inv, pointedConnectingHom_boundaryLift p 0 L,
    BoundaryLift.pointedFiberGroupEquiv_mk, pointedConnectingZero_boundaryLift _ V]
  change pointedFiberGroupEquiv p 0
    (loopZeroHomotopyEquiv (pointedFiber p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (boundaryLoop p V))) = _
  obtain ⟨U, hU, hend⟩ := exists_standard_common p t N L
  have he := boundaryLoop_zero_inverse_common p V U hU
  rw [hend] at he
  exact he

end
end SerrePositivity.KST.Spectra.LoopConnectingComparison

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop による次数移動と連結射は零 loop 成分を経由して逆符号を伴って交換する。
方針：底の群の代表から二つの充填を選び、共通 path と隣接比較ホーンによる逆元公式へ帰着する。
規約：入力は loop 空間の基本群。出力は fiber の基本群で比較する。
使われ方：Goerss–Jardine I §8、VIII §1。係数微分の loop との交換の符号。 -/
theorem pointedConnectingZero_loopZero {E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) [Fibration p.right] [KanComplex E.right] [KanComplex B.right]
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).basepoint) :
    loopZeroHomotopyEquiv (pointedFiber p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 (loopPointedFiberIso p).inv.right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (loopPointedFiberIso p).inv)
        (pointedConnectingZero (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p) a)) =
      (pointedConnectingHom p 0 (loopPositiveHomotopyEquiv B 0 a))⁻¹ := by
  let eb := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 1 (Iso.refl B.right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)
  let b := eb.symm (loopPositiveHomotopyEquiv B 0 a)
  obtain ⟨s, hs⟩ := Quotient.mk_surjective b
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = b at hs
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p.right E.basepoint s
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift (pathEndpoint B).right (basedPathSpace B).basepoint
    (LoopConnectingComparison.pathBaseSimplex p s)
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift
    (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace E).basepoint (LoopConnectingComparison.sourceLoop p s M)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 1 (Iso.refl B.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
      loopPositiveHomotopyEquiv B 0 a := by
    rw [hs]
    exact eb.apply_symm_apply _
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint
        (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (LoopConnectingComparison.sourceLoop p s M)) = a := by
    apply (loopPositiveHomotopyEquiv B 0).injective
    rw [LoopConnectingComparison.sourceLoop_positive, hb]
  have he := LoopConnectingComparison.pointedConnecting_zero_loop_representative p s M L V
  rw [ha, hb] at he
  exact he

end
end SerrePositivity.KST.Spectra
