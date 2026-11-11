module

public import SerrePositivity.KST.Spectra.SkeletalFiberDifferential
public import SerrePositivity.KST.Spectra.SkeletalFiberCoefficientGroups

/-!
概要：骨格の fiber の微分を非退化単体上の高次係数の関数群へ移す。
方針：証明済みの fiber の群同型で幾何的な微分を共役する。
規約：交代 cochain 微分との一致、符号、収束はまだ主張しない。
使われ方：Goerss–Jardine VIII §1。塔の微分と正規化 cochain の比較の準備。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) (X : PointedSimplicialSet.{u}) [KanComplex X.right]

/-- 概要：非退化 n+1 単体を添字とする高次係数の関数群。
方針：fiber の群の計算の標的に名前を付ける。
規約：係数の実際の次数は n+r+2。
使われ方：Goerss–Jardine VIII §1。塔の微分を係数へ移す群。 -/
abbrev coefficientGroup (n r : ℕ) :=
  K.nonDegenerate (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right (n + 1 + r) X.basepoint

/-- 概要：実際の骨格の微分をセルごとの係数へ移した群準同型。
方針：始域の fiber の群同型の逆、幾何的微分、終域の群同型を合成する。
規約：二つの表示の係数次数は算術的に同じ。交代式との一致は別に証明する。
使われ方：Goerss–Jardine VIII §1。有理 Shapiro の微分の計算の対象。 -/
def coefficientDifferential (n r : ℕ) :
    coefficientGroup K X n (r + 1) →* coefficientGroup K X (n + 1) r :=
  (stageFiberCoefficientEquiv K X (n + 1) r).toMonoidHom.comp
    ((UnbasedPointedMapping.stageDifferential K X n r).comp
      (stageFiberCoefficientEquiv K X n (r + 1)).symm.toMonoidHom)

lemma coefficientDifferential_apply (n r : ℕ) (a : coefficientGroup K X n (r + 1)) :
    coefficientDifferential K X n r a =
      stageFiberCoefficientEquiv K X (n + 1) r
        (UnbasedPointedMapping.stageDifferential K X n r
          ((stageFiberCoefficientEquiv K X n (r + 1)).symm a)) := rfl

/-- 概要：fiber の群の表示は幾何的微分と移された係数微分を交換する。
方針：始域の群同型の順逆を打ち消す。
規約：群同型そのものによる可換式。
使われ方：Goerss–Jardine VIII §1。係数微分を幾何的な微分へ戻す界面。 -/
lemma stageFiberCoefficientEquiv_differential (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K X n).right (r + 1)
      (UnbasedPointedMapping.stageFiber K X n).basepoint) :
    coefficientDifferential K X n r (stageFiberCoefficientEquiv K X n (r + 1) a) =
      stageFiberCoefficientEquiv K X (n + 1) r
        (UnbasedPointedMapping.stageDifferential K X n r a) := by
  rw [coefficientDifferential_apply, MulEquiv.symm_apply_apply]

/-- 概要：セルの係数に移した骨格の微分の二乗は自明。
方針：中間の群同型を打ち消し、実際の fiber の微分の零合成を使う。
規約：この零合成だけから通常の cochain の式との一致を主張しない。
使われ方：Goerss–Jardine VIII §1。係数に移した E_1 の複体条件。 -/
@[simp]
theorem coefficientDifferential_comp (n r : ℕ) (a : coefficientGroup K X n (r + 2)) :
    coefficientDifferential K X (n + 1) r (coefficientDifferential K X n (r + 1) a) = 1 := by
  rw [coefficientDifferential_apply, coefficientDifferential_apply,
    MulEquiv.symm_apply_apply, UnbasedPointedMapping.stageDifferential_comp, map_one]

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
