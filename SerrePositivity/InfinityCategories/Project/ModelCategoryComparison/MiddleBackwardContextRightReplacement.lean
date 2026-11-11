module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextMiddleProperty
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPrecomp

/-!
# 任意の前後の語を持つ元の全部分圏上の右置換

概要：元の中央自明 cofibration の全部分圏で右置換と実際の unit を構成する。
方針：元の局所図式と前後の図式を包含で制限し、動く接合点で貼る。
規約：中央の実際の列の条件から入力の自明性を証明する。
使われ方：元の恒等列の挿入への本質像の持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n m : ℕ) (X Y : C)

def sourceFamily := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).precomp (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y)

lemma sourceFamily_middle_trivial (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y) :
    trivialCofibrations C ((sourceFamily a b n m X Y).middle.app S) :=
  (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextMiddleProperty.middleColumn_property a b n m X Y (trivialCofibrations C) S.obj).1 S.property

def sourcePrefix := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.prefixDiagram a b n m X Y).precomp (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y)

def sourceSuffix := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.suffixDiagram a b n m X Y).precomp (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y)

def sourceRebuiltDiagram := ((sourcePrefix a b n m X Y).append
  (sourceFamily a b n m X Y).movingDiagram).append (sourceSuffix a b n m X Y)

def sourceRebuiltFunctor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) X Y :=
  (sourceRebuiltDiagram a b n m X Y).fixedFunctor

lemma sourceRebuiltFunctor_eq : sourceRebuiltFunctor a b n m X Y = _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y := by
  change _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.rebuiltFunctor a b n m X Y = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuiltFunctor_eq]
  rfl

def rightDiagram := ((sourcePrefix a b n m X Y).append
  ((sourceFamily a b n m X Y).pushoutDiagram
    (sourceFamily_middle_trivial a b n m X Y))).append (sourceSuffix a b n m X Y)

def rightReplacement : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) X Y :=
  (rightDiagram a b n m X Y).fixedFunctor

def rebuiltUnit : sourceRebuiltFunctor a b n m X Y ⟶ rightReplacement a b n m X Y :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom.id (sourcePrefix a b n m X Y)).append
    ((sourceFamily a b n m X Y).pushoutUnit (sourceFamily_middle_trivial a b n m X Y))).append
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom.id (sourceSuffix a b n m X Y))).natTrans

def rightUnit : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y ⟶ rightReplacement a b n m X Y :=
  eqToHom (sourceRebuiltFunctor_eq a b n m X Y).symm ≫ rebuiltUnit a b n m X Y

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement
