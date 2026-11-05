module
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTargetAdjunction

public import SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTargetContraction
public import SerrePositivity.KST.LocalizingInvariants.RetractionHomotopyAdjunction

/-!
概要：矢印圏の元の終点評価は恒等矢印関手の実左随伴。
方針：max による収縮の前後合成を厳密に計算し、h Fun 全体の三角恒等式へ渡す。
規約：始域に安定性を要求しない。使われ方：cofiber 回転を経た Cone の実右随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ArrowTarget

variable (X : SSet.{u})

/-- 元の終点評価と恒等矢印関手の間の実随伴。 -/
def adjunction [Quasicategory X] : QCatAdjunction (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target X) (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.identityArrow X) :=
  adjunctionOfRetractionHomotopy (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.identityArrow_target X) (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.unitHomotopy X)
    (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.contraction_target X) (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowTarget.identityArrow_contraction X)

end SerrePositivity.KST.LocalizingInvariants.ArrowTarget
