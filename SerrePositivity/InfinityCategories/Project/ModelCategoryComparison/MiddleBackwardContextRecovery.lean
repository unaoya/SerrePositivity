module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractMapRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramPartRecovery

/-!
# 任意の前後の語の中の置換を元の恒等図式へ戻す

概要：全対象と全縦射の再構成を照合し、置換の比較を元の恒等図式へ接続する。
方針：局所ブロックの回収と二度の前後分割の回収を合成する。
規約：元の任意の前後の語、全体の固定端点、動く局所接合点を保持する。
使われ方：中央 backward 列の全部分圏への第一の包含の比較。
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

lemma rebuiltDiagram_eq : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.rebuiltDiagram a b n m X Y = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.originalDiagram a b n m X Y := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.rebuiltDiagram _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractMapRecovery.rebuildDiagram_eq]
  change (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.originalDiagram a b n m X Y).leftPart.leftPart).append
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.originalDiagram a b n m X Y).leftPart.rightPart).append
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.originalDiagram a b n m X Y).rightPart = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_parts, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_parts]

lemma rebuiltFunctor_eq : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.rebuiltFunctor a b n m X Y =
    𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) X Y) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.rebuiltFunctor
  rw [rebuiltDiagram_eq]
  rfl

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

def pullbackOriginalCounit : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.pullbackFunctor a b n m X Y cof ⟶
    𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.pullbackCounit a b n m X Y cof ≫ eqToHom (rebuiltFunctor_eq a b n m X Y)

variable (hc : ∀ S, trivialCofibrations C ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).middle.app S))

def pushoutOriginalUnit : 𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.pushoutFunctor a b n m X Y hc :=
  eqToHom (rebuiltFunctor_eq a b n m X Y).symm ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.pushoutUnit a b n m X Y hc

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
