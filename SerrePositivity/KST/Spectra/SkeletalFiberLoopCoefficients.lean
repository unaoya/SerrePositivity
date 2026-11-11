module

public import SerrePositivity.KST.Spectra.CellMappingCoordinates
public import SerrePositivity.KST.Spectra.SimplexCellLoopComponents

/-!
概要：骨格 fiber の基本群の係数と loop 値の球面の連結成分の係数の一致。
方針：セル商からの loop 写像類を基本群へ移し、同じセルへの制限で両者を比較する。
規約：既存の正次数の群同型と同じ符号・同じ球面の向きを使用する。
使われ方：Goerss–Jardine I §7、VIII §1。微分の計算を成分の代表計算へ移す基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セル商からの loop 写像類と実際の骨格 fiber の基本群の群同型。
方針：loop 写像類の群同型と厳密な fiber の同型を合成する。
規約：群構造は既存の基本群との比較から供給される。
使われ方：Goerss–Jardine I §7、VIII §1。成分計算を正次数へ接続する。 -/
def stageFiberLoopClassEquiv (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) :
    LoopMappingClasses (cellCofiber K (n + 1)) Y ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
        (UnbasedPointedMapping.stageFiber K Y n).basepoint := by
  let e : (PointedObject.basedHom (cellCofiber K (n + 1)) Y).right ≅
      (UnbasedPointedMapping.stageFiber K Y n).right :=
    PointedSimplicialSet.forget.mapIso (stageFiberCellIso K Y n)
  exact (LoopMappingClasses.groupEquiv (cellCofiber K (n + 1)) Y).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 e
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (stageFiberCellIso K Y n).hom))

/-- 概要：fiber の基本群の既存係数は loop 値の成分係数から同じ符号で得られる。
方針：両方を同一のセルへの制限へ戻し、源の自然性と球面の基本段の公式を使う。
規約：球面次元 n+1 に loop の一次元を加えた π_(n+2) を得る。
使われ方：Goerss–Jardine VIII §1。成分と正次数の係数表示の符号の照合。 -/
theorem stageFiberCoefficientEquiv_loopClass (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) (a : LoopMappingClasses (cellCofiber K (n + 1)) Y)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K Y n 0 (stageFiberLoopClassEquiv K Y n a) s =
      CirclePower.positiveHomotopyEquiv Y n
        (SimplexCell.componentEquiv (PointedObject.basedHom CirclePower.space.{u} Y) n
          (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
            (cellSphereInclusion K (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s))
            (PointedObject.basedHom CirclePower.space Y)).right a)) := by
  change stageFiberCoefficientEquiv K Y n 0
    (pointedGroupMap 0 (stageFiberCellIso K Y n).hom
      (LoopMappingClasses.groupEquiv (cellCofiber K (n + 1)) Y a)) s = _
  rw [stageFiberCoefficientEquiv_restriction,
    ← pointedGroupMap_comp 0 (stageFiberCellIso K Y n).hom (stageFiberCellIso K Y n).inv,
    Iso.hom_inv_id, pointedGroupMap_id]
  have h := LoopMappingClasses.classEquiv_pre
    (cellSphereInclusion K (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) Y a
  change SimplexCell.positiveHomotopyEquiv Y n 0
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (cellSphereInclusion K (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) Y).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
      (LoopMappingClasses.classEquiv (cellCofiber K (n + 1)) Y a)) = _
  rw [← h]
  exact SimplexCell.positiveHomotopyEquiv_zero_loopClasses Y n _

/-- 概要：loop 値の骨格 fiber の成分と元の骨格 fiber の基本群の同値。
方針：loop 値の fiber をセル商からの写像空間に戻し、loop 写像類の群比較を使う。
規約：loop は CirclePower.space の内部 Hom による模型。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的成分の計算を基本群の係数へ移す。 -/
def stageFiberLoopComponentEquiv (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) :
    π₀ (UnbasedPointedMapping.stageFiber K
      (PointedObject.basedHom CirclePower.space.{u} Y) n).right ≃
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
          (UnbasedPointedMapping.stageFiber K Y n).basepoint :=
  (π₀Functor.mapIso (PointedSimplicialSet.forget.mapIso
    (stageFiberCellIso K (PointedObject.basedHom CirclePower.space.{u} Y) n).symm)).toEquiv.trans
      (stageFiberLoopClassEquiv K Y n).toEquiv

/-- 概要：loop 値の成分比較から元の基本群の係数比較への正符号の可換式。
方針：成分係数も基本群係数も同じセル球面への制限で計算する。
規約：すべてのセルの係数を同時に比較し、添字集合の有限性を仮定しない。
使われ方：Goerss–Jardine VIII §1。連結準同型と成分の障害計算の比較の基本段。 -/
theorem stageFiberCoefficientEquiv_loopComponent (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : π₀ (UnbasedPointedMapping.stageFiber K
      (PointedObject.basedHom CirclePower.space.{u} Y) n).right)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K Y n 0 (stageFiberLoopComponentEquiv K Y n a) s =
      CirclePower.positiveHomotopyEquiv Y n
        (stageFiberComponentEquiv K (PointedObject.basedHom CirclePower.space.{u} Y) n a s) := by
  change stageFiberCoefficientEquiv K Y n 0
    (stageFiberLoopClassEquiv K Y n
      (mapπ₀ (stageFiberCellIso K (PointedObject.basedHom CirclePower.space.{u} Y) n).inv.right a))
        s = _
  rw [stageFiberCoefficientEquiv_loopClass, stageFiberComponentEquiv_restriction]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
