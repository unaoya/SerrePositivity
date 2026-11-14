module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardTrivialRightReplacement
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenActionObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingFull

/-!
# 元の中央恒等列の挿入と全部分圏への持ち上げ

概要：中央を飛ばす元の語の単射による WordAction を、自明中央列の全部分圏へ移す。
方針：空 fiber の中央列は元の等式の移送射であり、元の挿入は全忠実である。
規約：既存の語の作用そのものを使う。別の写像で代用しない。
使われ方：右置換の unit による第二の nerve 比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

abbrev sourceWord (n m : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m)
abbrev wordMap (n m : ℕ) : sourceWord n m ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) .backward

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def originalFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (sourceWord n m) X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (wordMap n m)

instance originalFunctor_full :
    (originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Full :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_full _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_injective _ _ _)

instance originalFunctor_faithful :
    (originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Faithful :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor_faithful _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_injective _ _ _)

lemma originalFunctor_middle_trivial (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (sourceWord n m) X Y) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.property (originalFunctor.obj S) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_cut_inserted (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) .backward
  have he := (wordMap n m).cut_source_target_of_eq (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m) h
  change trivialCofibrations C (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column (wordMap n m) S (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m))
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column_eqToHom_of_cut_eq (wordMap n m) S
    (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m) h he
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column (wordMap n m) S (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m)) := by
    rw [hc]
    infer_instance
  exact (trivialCofibrations C).of_isIso _

def functor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (sourceWord n m) X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects (C := C) (n := n) (m := m) (X := X) (Y := Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.property.lift originalFunctor originalFunctor_middle_trivial

lemma functor_comp_inclusion : functor (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion = originalFunctor := rfl

instance functor_full : (functor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Full := by
  have : (functor (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion).Full := inferInstanceAs originalFunctor.Full
  exact Functor.Full.of_comp_faithful _ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion

instance functor_faithful :
    (functor (C := C) (n := n) (m := m) (X := X) (Y := Y)).Faithful := by
  have : (functor (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion).Faithful := inferInstanceAs originalFunctor.Faithful
  exact Functor.Faithful.of_comp _ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion
