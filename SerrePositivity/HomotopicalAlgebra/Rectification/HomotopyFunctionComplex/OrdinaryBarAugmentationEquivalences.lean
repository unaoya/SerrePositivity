module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftPadding

/-!
# 中断した任意モデル源への一般化：OrdinaryBarAugmentationEquivalences

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Both original simplex augmentations in the ordinary bar evaluation square are inverted。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0134][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0134
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Both original simplex augmentations in the ordinary bar evaluation square are inverted

The explicit source lift and the original small-output padding are
retained. No equivalence of the evaluation or of the row map is assumed.
-/

@[expose] public section
universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

def sourceIso : SSet.uliftFunctor.{max u v, max u v}.obj
    (nerve (OrdinaryBarTotalCone.Index R)) ≅
      SimplexNerve.functor.obj (OrdinaryBarEvaluation.bar R) :=
  NatIso.ofComponents (fun _ =>
    { toFun := fun x => x.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl : _ ≃ _ }.toIso) (by intro _ _ _; rfl)

lemma large_eq : OrdinaryBarNerveBridge.simplexAugmentation R =
    (sourceIso R).hom ≫ SimplexNerve.augmentation.app (OrdinaryBarEvaluation.bar R) := rfl

lemma large_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarNerveBridge.simplexAugmentation R)) := by
  have := SimplexNerve.augmentation_localized_isIso (OrdinaryBarEvaluation.bar R)
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (SimplexNerve.augmentation.app (OrdinaryBarEvaluation.bar R))) := this
  rw [large_eq, CategoryTheory.Functor.map_comp]
  infer_instance

lemma small_eq : OrdinaryBarEvaluatedEndpoint.smallAugmentation R =
    SSet.uliftFunctor.{max u v, v}.map
      (SimplexNerve.augmentation.app (BarOutput.output R)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.paddingIso.{v, u}.app (BarOutput.output R)).inv := rfl

lemma small_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarEvaluatedEndpoint.smallAugmentation R)) := by
  have := UniverseLift.anodyneQ_map_isIso_of_small.{max u v, v}
    (SimplexNerve.augmentation.app (BarOutput.output R))
    (SimplexNerve.augmentation_localized_isIso _)
  have : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{max u v, v}.map
      (SimplexNerve.augmentation.app (BarOutput.output R)))) := this
  rw [small_eq, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences
