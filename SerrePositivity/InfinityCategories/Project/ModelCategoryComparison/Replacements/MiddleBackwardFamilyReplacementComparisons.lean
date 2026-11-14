module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyNatTrans

/-!
# 元の全体の図式に対する置換の counit と unit

概要：左への pullback の射影と右への pushout の包含を、全体の自然変換にする。
方針：元の自然な二つの射列の比較を、中央の分解式と端点回収式で整合させる。
規約：元の全体の X,Y を固定し、全頂点の縦射を弱同値に保つ。
使われ方：二つの充満部分圏の nerve 比較へ渡す実際の自然変換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyReplacementComparisons
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y)

def pullbackCounitData
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyHom.Hom (F.pullbackFamily cof) F where
  left := F.pullbackLeftProjection cof
  right := 𝟙 F.right
  left_mem d i := (F.pullbackLeftProjection_trivialFibration cof d i).2
  right_mem _ i := (weakEquivalences C).id_mem _
  a_comm := rfl
  middle_comm := by
    apply NatTrans.ext
    funext d
    change (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.first cof (F.middle.app d) ≫ eqToHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last ((F.pullbackInputs cof).obj d)).symm) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection ((F.pullbackInputs cof).obj d)).app (Fin.last n) =
      𝟙 _ ≫ F.middle.app d
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection_last]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.fac cof (F.middle.app d)
  b_comm := by
    apply NatTrans.ext
    funext d
    change F.b.app d ≫ 𝟙 _ = F.b.app d
    exact Category.comp_id _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyReplacementComparisons (pullbackCounitData)


def pullbackCounit
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    F.pullbackFunctor cof ⟶ F.zigzagFunctor := (F.pullbackCounitData cof).natTrans

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyReplacementComparisons (pullbackCounit)


def pushoutUnitData (hc : ∀ d, trivialCofibrations C (F.middle.app d)) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyHom.Hom F (F.pushoutFamily hc) where
  left := 𝟙 F.left
  right := F.pushoutRightInclusion
  left_mem _ i := (weakEquivalences C).id_mem _
  right_mem d i := (F.pushoutRightInclusion_trivialCofibration hc d i).2
  a_comm := by
    apply NatTrans.ext
    funext d
    change 𝟙 _ ≫ F.a.app d = F.a.app d
    exact Category.id_comp _
  middle_comm := by
    apply NatTrans.ext
    funext d
    change F.middle.app d ≫ 𝟙 _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion (F.pushoutInputs.obj d)).app 0 ≫ 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion_zero]
    rfl
  b_comm := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyReplacementComparisons (pushoutUnitData)


def pushoutUnit (hc : ∀ d, trivialCofibrations C (F.middle.app d)) :
    F.zigzagFunctor ⟶ F.pushoutFunctor hc := (F.pushoutUnitData hc).natTrans

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyReplacementComparisons (pushoutUnit)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyReplacementComparisons
