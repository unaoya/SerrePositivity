module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardTrivialCofibration
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyPrecomp

/-!
# 元の中央自明 cofibration の全部分圏上の右置換

概要：元の全部分圏から右置換図式を構成し、元の包含からの実際の unit を得る。
方針：元の抽出図式を包含へ前合成し、再構成との厳密な同定で元の始域へ戻す。
規約：中央の実際の列の自明性を用いる。恒等列の挿入との同定は後続。
使われ方：中央 backward 恒等列の挿入の第二の nerve 比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement
open CategoryTheory CategoryTheory.Limits _root_.HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def sourceFamily : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects (C := C) (n := n) (m := m) (X := X) (Y := Y)) C n m X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.precomp _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion

lemma sourceFamily_middle_trivial (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    trivialCofibrations C (sourceFamily.middle.app S) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.middleColumn_property (trivialCofibrations C) S.obj)
  change trivialCofibrations C ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuilt S.obj).arrow (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MiddleBackward.Positions.middleColumn n m)) ↔
    trivialCofibrations C (sourceFamily.middle.app S) at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows.rebuilt_eq] at h
  exact h.mp S.property

def rightReplacement : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects (C := C) (n := n) (m := m) (X := X) (Y := Y) ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y :=
  sourceFamily.pushoutFunctor sourceFamily_middle_trivial

def rightUnit : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion (C := C) (n := n) (m := m) (X := X) (Y := Y) ⟶ rightReplacement :=
  Functor.whiskerLeft _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildMaps.rebuildIso.inv ≫
    sourceFamily.pushoutUnit sourceFamily_middle_trivial

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement
