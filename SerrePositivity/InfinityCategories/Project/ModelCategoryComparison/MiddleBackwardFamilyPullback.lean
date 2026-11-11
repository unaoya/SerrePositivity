module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFactorizationInput

/-!
# 中央の列を自明 cofibration にする図式全体の置換

概要：同じ関手的分解の第一因子を中央の脚とする新しい全体の zigzag 関手。
方針：左の射列を同時 pullback し、自然な射影と正規化した端点を使う。
規約：元の X,Y と右ブロックを保持する。proper 性・cofibrancy は不要。
使われ方：中央の自明 cofibration の充満部分圏への関手的置換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPullback
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

def pullbackMiddle :
    F.right ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m 0 ⟶ F.pullbackLeft cof ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n (Fin.last n) where
  app d := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.first cof (F.middle.app d) ≫
    eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last ((F.pullbackInputs cof).obj d)).symm
  naturality d d' f := by
    change (F.right.map f).app 0 ≫
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.first cof (F.middle.app d') ≫ eqToHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last ((F.pullbackInputs cof).obj d')).symm) =
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.first cof (F.middle.app d) ≫ eqToHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last ((F.pullbackInputs cof).obj d)).symm) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackComparison ((F.pullbackInputs cof).map f)).app (Fin.last n)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackComparison_last]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have h := cof.i.naturality (F.middleArrow.map f)
    change (F.right.map f).app 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.first cof (F.middle.app d') =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.first cof (F.middle.app d) ≫ cof.Z.map (F.middleArrow.map f) at h
    rw [← Category.assoc, h, Category.assoc]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPullback (pullbackMiddle)


def pullbackOuterLeft : F.pullbackLeft cof ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n 0 ⟶ (Functor.const D).obj X :=
  Functor.whiskerRight (F.pullbackLeftProjection cof) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n 0) ≫ F.a

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPullback (pullbackOuterLeft)


lemma pullbackMiddle_trivialCofibration (d : D) :
    trivialCofibrations C ((F.pullbackMiddle cof).app d) :=
  (trivialCofibrations C).comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization.first_trivialCofibration cof (F.middle.app d) (F.middle_mem d))
    ((trivialCofibrations C).of_isIso _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPullback (pullbackMiddle_trivialCofibration)


def pullbackFamily : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y where
  left := F.pullbackLeft cof
  right := F.right
  a := F.pullbackOuterLeft cof
  middle := F.pullbackMiddle cof
  b := F.b
  a_mem d := (weakEquivalences C).comp_mem _ _
    (F.pullbackLeftProjection_trivialFibration cof d 0).2 (F.a_mem d)
  middle_mem d := (F.pullbackMiddle_trivialCofibration cof d).2
  b_mem := F.b_mem
  left_mem := F.pullbackLeft_map_weak cof
  right_mem := F.right_mem

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPullback (pullbackFamily)


def pullbackFunctor : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y :=
  (F.pullbackFamily cof).zigzagFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPullback (pullbackFunctor)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPullback
