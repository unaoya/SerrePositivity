module

public import SerrePositivity.KST.Spectra.SimplexCellLoopPositive
public import SerrePositivity.KST.Spectra.SkeletalFiberLoopCoefficients

/-!
概要：骨格 fiber の正次数群の loop 値比較と既存の係数表示の整合性。
方針：厳密なセル商の表示を通して写像空間の loop 比較を適用する。
規約：全正次数の群同型と各セルの係数を同じ符号で比較する。
使われ方：Goerss–Jardine VIII §1。成分の代表計算から高次数の微分比較への次数帰納。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop 値の骨格 fiber の π_(r+1) と元の fiber の π_(r+2) の群同型。
方針：両方の fiber をセル商の写像空間へ移し、loop の正次数比較を合成する。
規約：基点と群演算を保存する既存の同型の合成。
使われ方：Goerss–Jardine I §7、VIII §1。全正次数の比較の反復。 -/
def stageFiberLoopPositiveEquiv (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right r
        (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right (r + 1)
        (UnbasedPointedMapping.stageFiber K Y n).basepoint := by
  let eL : (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right ≅
      (PointedObject.basedHom (cellCofiber K (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right :=
    PointedSimplicialSet.forget.mapIso (stageFiberCellIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).symm
  let eY : (PointedObject.basedHom (cellCofiber K (n + 1)) Y).right ≅
      (UnbasedPointedMapping.stageFiber K Y n).right :=
    PointedSimplicialSet.forget.mapIso (stageFiberCellIso K Y n)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r eL
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (stageFiberCellIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).inv)).trans
      ((PointedMapping.loopPositiveEquiv (cellCofiber K (n + 1)) Y r).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) eY
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (stageFiberCellIso K Y n).hom)))

lemma stageFiberLoopPositiveEquiv_apply (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right r
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint) :
    stageFiberLoopPositiveEquiv K Y n r a =
      pointedGroupMap (r + 1) (stageFiberCellIso K Y n).hom
        (PointedMapping.loopPositiveEquiv (cellCofiber K (n + 1)) Y r
          (pointedGroupMap r (stageFiberCellIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).inv a)) := rfl

/-- 概要：全正次数で骨格 fiber の係数表示は loop 値比較と正符号で可換。
方針：両辺を同じセル球面への制限へ戻し、源の自然性と球面の帰納式を使う。
規約：各セルの係数の等式。像と符号を保ち、零性だけの比較に弱めない。
使われ方：Goerss–Jardine VIII §1。塔の微分を高次数で同定するための比較。 -/
theorem stageFiberCoefficientEquiv_loopPositive (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right r
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K Y n (r + 1) (stageFiberLoopPositiveEquiv K Y n r a) s =
      loopPositiveHomotopyEquiv Y (n + 1 + r)
        (stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r a s) := by
  rw [stageFiberLoopPositiveEquiv_apply, stageFiberCoefficientEquiv_restriction,
    ← pointedGroupMap_comp (r + 1) (stageFiberCellIso K Y n).hom (stageFiberCellIso K Y n).inv,
    Iso.hom_inv_id, pointedGroupMap_id, ← PointedMapping.loopPositiveEquiv_pre,
    SimplexCell.positiveHomotopyEquiv_loopPositive, stageFiberCoefficientEquiv_restriction]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
