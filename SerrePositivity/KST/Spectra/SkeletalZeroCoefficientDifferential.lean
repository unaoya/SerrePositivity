module

public import SerrePositivity.KST.Spectra.SkeletalFiberLoopZero
public import SerrePositivity.KST.Spectra.SkeletalCoefficientDifferential

/-!
概要：基本群側の実際の係数微分を、通常の loop 値の成分微分の係数で計算する。
方針：微分の反可換式と成分係数の逆元公式を合成し、二つの逆元を打ち消す。
規約：零性だけでなく各セルの値そのものを比較する。
使われ方：Goerss–Jardine VIII §1。正規化交代微分との同定の基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：実際の係数微分の基本段は loop 値の成分微分の係数と正符号で対応する。
方針：fiber の反可換式と零 loop の係数比較の逆元を、同じ係数の上で二回消す。
規約：入力は loop 値の骨格 fiber の任意の基本群の元。
使われ方：Goerss–Jardine VIII §1。成分での幾何的障害計算を群の微分へ運ぶ。 -/
theorem coefficientDifferential_zero_component (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).right 0
      (UnbasedPointedMapping.stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n).basepoint)
    (s : K.nonDegenerate (n + 1 + 1)) :
    coefficientDifferential K Y n 0
        (fun t ↦ loopPositiveHomotopyEquiv Y (n + 1)
          (stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n 0 a t)) s =
      loopPositiveHomotopyEquiv Y (n + 1)
        (stageFiberComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1)
          (UnbasedPointedMapping.stageComponentDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n a) s) := by
  have hin : (fun t ↦ loopPositiveHomotopyEquiv Y (n + 1)
      (stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n 0 a t)) =
      stageFiberCoefficientEquiv K Y n 1 (stageFiberLoopPositiveEquiv K Y n 0 a) := by
    funext t
    exact (stageFiberCoefficientEquiv_loopPositive K Y n 0 a t).symm
  rw [hin, stageFiberCoefficientEquiv_differential]
  have h := congrArg (fun z ↦ stageFiberCoefficientEquiv K Y (n + 1) 0 z s)
    (stageComponentDifferential_loopZero K Y n a)
  rw [stageFiberCoefficientEquiv_loopZero, map_inv, Pi.inv_apply] at h
  have hh := congrArg Inv.inv h
  simp only [inv_inv] at hh
  exact hh.symm

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
