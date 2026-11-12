module

public import SerrePositivity.KST.Spectra.SkeletalZeroDifferential
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyComponents

/-!
概要：骨格の零次数微分を、基点に依存しない連結成分へ移す。
方針：零次数の商と π₀ の自然同値を、通常の loop の fiber 比較へ合成する。
規約：CirclePower.space の Kan 置換を用いた既存比較とは別に名前を付ける。
使われ方：Goerss–Jardine VIII §1。成分係数の幾何的計算への接続。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 基本群から次の骨格 fiber の連結成分への微分。 -/
def UnbasedPointedMapping.stageComponentDifferential (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K Y n).right 0 (stageFiber K Y n).basepoint →
      π₀ (stageFiber K Y (n + 1)).right :=
  fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (stageDifferentialZero K Y n a)

namespace SkeletalCellAttachment

/-- 通常の circle 値の骨格 fiber の π₀ と元の fiber の基本群の同値。 -/
def stageFiberOrdinaryLoopComponentEquiv (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    π₀ (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right 0
        (UnbasedPointedMapping.stageFiber K Y n).basepoint :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right)
    (x := (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint)).symm.trans
      (stageFiberLoopZeroEquiv K Y n)

/-- 零次数の商の比較を連結成分へ移すと、元の零次数比較に戻る。 -/
@[simp]
lemma stageFiberOrdinaryLoopComponentEquiv_zero (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right 0
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint) :
    stageFiberOrdinaryLoopComponentEquiv K Y n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero a) =
      stageFiberLoopZeroEquiv K Y n a := by
  exact congrArg (stageFiberLoopZeroEquiv K Y n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm_apply_apply a)

/-- 概要：実際の成分への骨格微分は基本群側の微分と逆符号で交換する。
方針：零次数の商と π₀ の同値の順逆を消し、既証の零次数の反可換式を適用する。
規約：ここでの通常の circle の比較の向きを保持する。
使われ方：Goerss–Jardine VIII §1。成分代表の障害と正次数微分の接続。 -/
theorem stageComponentDifferential_loopZero (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right 0
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint) :
    stageFiberOrdinaryLoopComponentEquiv K Y (n + 1)
      (UnbasedPointedMapping.stageComponentDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n a) =
    (UnbasedPointedMapping.stageDifferential K Y n 0
      (stageFiberLoopPositiveEquiv K Y n 0 a))⁻¹ := by
  change stageFiberOrdinaryLoopComponentEquiv K Y (n + 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
      (UnbasedPointedMapping.stageDifferentialZero K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n a)) = _
  rw [stageFiberOrdinaryLoopComponentEquiv_zero, stageDifferential_loopZero]

end SkeletalCellAttachment
end
end SerrePositivity.KST.Spectra
