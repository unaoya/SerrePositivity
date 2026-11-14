module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardContextRecovery
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardMovingFamilyColumnProperty

/-!
# 任意の前後の語の中の元の中央列の自明性

概要：左置換の中央列は、元の全体の同じ位置で自明 cofibration となる。
方針：前後の語の連結による移送と局所図式の中央列の移送を消去する。
規約：元の全体の語と列の番号を明示し、別の代表に置き換えない。
使われ方：実際の全体の全部分圏への置換の着地。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n m : ℕ) (X Y : C)

def middleColumn : Fin (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m).length :=
  ((_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m).natAdd a.length).castAdd b.length

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

lemma pullback_middle_trivial (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) X Y) :
    trivialCofibrations C
      (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.pullbackFunctor a b n m X Y cof).obj S).arrow (middleColumn a b n m)) := by
  change trivialCofibrations C ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.prefixDiagram a b n m X Y).obj S)
      (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).pullbackFamily cof).zigzagObj S))
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.suffixDiagram a b n m X Y).obj S)).arrow (middleColumn a b n m))
  dsimp only [middleColumn]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property (trivialCofibrations C),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_right_property (trivialCofibrations C)]
  exact (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).pullbackFamily cof).middleColumn_property
    (trivialCofibrations C) S).2
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).pullbackMiddle_trivialCofibration cof S)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
