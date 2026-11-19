module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ArrowTargetAdjunction

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ArrowTargetContraction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.RetractionHomotopyAdjunction

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
def adjunction [Quasicategory X] : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.target X) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.identityArrow X) :=
  adjunctionOfRetractionHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.identityArrow_target X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.unitHomotopy X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.contraction_target X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.identityArrow_contraction X)

end SerrePositivity.KST.LocalizingInvariants.ArrowTarget
