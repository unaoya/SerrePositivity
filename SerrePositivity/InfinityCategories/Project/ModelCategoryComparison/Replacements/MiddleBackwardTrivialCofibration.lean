module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardRebuildMaps
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyColumnProperty
public import SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# 中央の列が自明 cofibration の全部分圏の元の nerve 比較

概要：元の固定語の中央の列を自明 cofibration に制限する包含は弱ホモトピー同値。
方針：元の graph から抽出した左置換を全部分圏へ戻し、元の恒等図式への counit を使う。
規約：同じ指定関手的分解を明示入力とする。単体集合のモデル構造は仮定しない。
使われ方：backward 恒等列の挿入の比較の第一工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def property : ObjectProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :=
  fun S => trivialCofibrations C (S.arrow (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m))

abbrev Objects := (property (C := C) (n := n) (m := m) (X := X) (Y := Y)).FullSubcategory

abbrev inclusion : Objects (C := C) (n := n) (m := m) (X := X) (Y := Y) ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y := property.ι

variable (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

def replacement : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y ⥤
    Objects (C := C) (n := n) (m := m) (X := X) (Y := Y) :=
  property.lift (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.pullbackFunctor cof) (fun S =>
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.pullbackFamily cof).middleColumn_property (trivialCofibrations C) S).2
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.pullbackMiddle_trivialCofibration cof S))

def counit : replacement cof ⋙ inclusion ⟶
    𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.family.pullbackCounit cof ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildMaps.rebuildIso.hom

include cof in
lemma inclusion_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (inclusion (C := C) (n := n) (m := m) (X := X) (Y := Y)))) :=
  _root_.SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.of_counit inclusion (replacement cof) (counit cof)

include cof in
lemma inclusion_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (inclusion (C := C) (n := n) (m := m) (X := X) (Y := Y))) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (inclusion_localized_isIso cof)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration
