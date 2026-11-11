module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPullback

/-!
# 中央の自明 cofibration を恒等列にする図式全体の置換

概要：右ブロックの同時 pushout により、中央が恒等列の動く端点の zigzag 図式を作る。
方針：同じ初点置換の comma 図式と正規化後の包含・端点自然性を使う。
規約：元の端点関手 A,B と左ブロックを保持する。長さ零と動く端点も含む。
使われ方：中央の恒等列の包含への関手的置換と unit の基礎データ。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B)

def pushoutInputs : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C m where
  obj d := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutInput (F.left.obj d) (F.right.obj d) (F.middle.app d)
  map f :=
    { left := F.right.map f
      right := (F.left.map f).app (Fin.last n)
      w := F.middle.naturality f }
  map_id d := by
    apply Comma.hom_ext
    · exact F.right.map_id d
    · change (F.left.map (𝟙 d)).app (Fin.last n) = 𝟙 _
      rw [F.left.map_id]
      rfl
  map_comp f g := by
    apply Comma.hom_ext
    · exact F.right.map_comp f g
    · change (F.left.map (f ≫ g)).app (Fin.last n) =
        (F.left.map f).app (Fin.last n) ≫ (F.left.map g).app (Fin.last n)
      rw [F.left.map_comp]
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutInputs)


def pushoutRight : D ⥤ ComposableArrows C m := F.pushoutInputs ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutRight)


def pushoutRightInclusion : F.right ⟶ F.pushoutRight where
  app d := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion (F.pushoutInputs.obj d)
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion_naturality (F.pushoutInputs.map f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutRightInclusion)


def pushoutMiddle :
    F.pushoutRight ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m 0 ⟶ F.left ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n (Fin.last n) where
  app d := 𝟙 ((F.left.obj d).obj (Fin.last n))
  naturality d d' f := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutComparison (F.pushoutInputs.map f)).app 0 ≫ 𝟙 _ =
      𝟙 _ ≫ (F.left.map f).app (Fin.last n)
    rw [Category.comp_id, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutComparison_zero]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutMiddle)


def pushoutOuterRight :
    B ⟶ F.pushoutRight ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m (Fin.last m) :=
  F.b ≫ Functor.whiskerRight F.pushoutRightInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m (Fin.last m))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutOuterRight)


variable (hc : ∀ d, trivialCofibrations C (F.middle.app d))

include hc in
lemma pushoutRightInclusion_trivialCofibration (d : D) (i : Fin (m + 1)) :
    trivialCofibrations C ((F.pushoutRightInclusion.app d).app i) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusion_trivialCofibration _ (hc d) i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutRightInclusion_trivialCofibration)


include hc in
lemma pushoutRight_map_weak {d d' : D} (f : d ⟶ d') (i : Fin (m + 1)) :
    weakEquivalences C ((F.pushoutRight.map f).app i) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutComparison_weakEquivalence _ (hc d) (hc d') (F.right_mem f) i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutRight_map_weak)


def pushoutFamily : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B where
  left := F.left
  right := F.pushoutRight
  a := F.a
  middle := F.pushoutMiddle
  b := F.pushoutOuterRight
  a_mem := F.a_mem
  middle_mem _ := (weakEquivalences C).id_mem _
  b_mem d := (weakEquivalences C).comp_mem _ _ (F.b_mem d)
    (F.pushoutRightInclusion_trivialCofibration hc d (Fin.last m)).2
  left_mem := F.left_mem
  right_mem := F.pushoutRight_map_weak hc
  endpoint_left_mem := F.endpoint_left_mem
  endpoint_right_mem := F.endpoint_right_mem

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutFamily)


def pushoutDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) A B :=
  (F.pushoutFamily hc).movingDiagram

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout (pushoutDiagram)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout
