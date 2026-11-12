module

public import SerrePositivity.KST.Spectra.SkeletalLoopDifferential
public import SerrePositivity.KST.Spectra.SkeletalCoefficientDifferential

/-!
概要：実際の骨格微分のセル係数は loop による次数移動と逆符号で交換する。
方針：骨格 fiber の反可換式を、既存の係数群同型の全射性で任意の係数へ移す。
規約：各非退化セルで値を比較する。零性だけの比較にはしない。
使われ方：Goerss–Jardine VIII §1。正規化微分との像・符号の同定の帰納段。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：係数に移した骨格の微分は loop の標準群同型と逆符号で交換する。
方針：任意の係数を fiber の群へ戻し、二つの係数表示の可換式と塔の反可換式を適用する。
規約：群の添字は実際の次数より一つ小さい。
使われ方：Goerss–Jardine VIII §1。微分の次数移動で生じる負符号。 -/
theorem coefficientDifferential_loopPositive (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (a : coefficientGroup K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n (r + 1))
    (t : K.nonDegenerate (n + 1 + 1)) :
    coefficientDifferential K Y n (r + 1)
        (fun s ↦ loopPositiveHomotopyEquiv Y (n + 1 + (r + 1)) (a s)) t =
    (loopPositiveHomotopyEquiv Y (n + 1 + 1 + r)
      (coefficientDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r a t))⁻¹ := by
  let x := (stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n (r + 1)).symm a
  have hx : stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n (r + 1) x = a :=
    (stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n (r + 1)).apply_symm_apply a
  have hin : (fun s ↦ loopPositiveHomotopyEquiv Y (n + 1 + (r + 1)) (a s)) =
      stageFiberCoefficientEquiv K Y n (r + 2)
        (stageFiberLoopPositiveEquiv K Y n (r + 1) x) := by
    funext s
    rw [stageFiberCoefficientEquiv_loopPositive, hx]
  rw [hin, stageFiberCoefficientEquiv_differential]
  have h := congrArg (fun z ↦ stageFiberCoefficientEquiv K Y (n + 1) (r + 1) z t)
    (stageDifferential_loopPositive K Y n r x)
  rw [stageFiberCoefficientEquiv_loopPositive, map_inv, Pi.inv_apply] at h
  have hout : coefficientDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r a =
      stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1) r
        (UnbasedPointedMapping.stageDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r x) := by
    rw [← hx, stageFiberCoefficientEquiv_differential]
  rw [← hout] at h
  simpa only [inv_inv] using (congrArg Inv.inv h).symm

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
