module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainUnits

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeChainUnits

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual endpoint units and unit-boundary formulas for all free-resolution degrees。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0174][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0174
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual endpoint units and unit-boundary formulas for all free-resolution degrees

The strong contraction equations are proved by the existing retract system.
All contraction parameters stay arbitrary in the endpoint unit formulas.
The original interval action is not assumed to be a strict monoid action.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarFreeChainTransfer
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {U : SSet.{max u v}} (j : U ⟶ parameters P n)

abbrev parameterContraction (X : D C) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :=
  RetractChainFamily.contraction (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) X t

lemma parameterContraction_zero (X : D C) :
    parameterContraction hcof hfib X (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U) =
      ParameterComposition.const U (𝟙 (ambient hcof hfib X)) :=
  RetractChainFamily.contraction_zero _ _ _ _ _ X U

lemma parameterContraction_one_right (X : D C) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    ParameterComposition.comp (parameterContraction hcof hfib X t)
      (parameterContraction hcof hfib X (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one U)) =
        parameterContraction hcof hfib X (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one U) :=
  RetractChainUnits.contraction_one_right (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) X t

lemma parameterContraction_one_left (X : D C) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    ParameterComposition.comp (parameterContraction hcof hfib X (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one U))
      (parameterContraction hcof hfib X t) =
        parameterContraction hcof hfib X (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one U) :=
  RetractChainUnits.contraction_one_left (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_on_section hcof hfib) X t

lemma trailing_identity {a : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    OrdinaryBarChainFamily.family hcof hfib
      (snoc hcof hfib P n j q (FreeGeneratorCategories.identity (D C) (n + 1) X) t) =
      OrdinaryBarChainFamily.family hcof hfib q := by
  rw [snoc, OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.trailing_identity (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) q t

lemma leading_identity {b : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib U X b) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (.nil : chain hcof hfib U X X)
        (FreeGeneratorCategories.identity (D C) (n + 1) X) t).append q) =
      OrdinaryBarChainFamily.family hcof hfib q := by
  rw [snoc, OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.leading_identity (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_on_section hcof hfib) q t

lemma interior_identity_after_zero {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)
    (r : chain hcof hfib U Y d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U))
        (FreeGeneratorCategories.identity (D C) (n + 1) Y) t).append r) =
      OrdinaryBarChainFamily.family hcof hfib ((snoc hcof hfib P n j q f t).append r) := by
  unfold snoc
  rw [OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.interior_identity_after_zero (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) q _ t r

lemma interior_identity_at_zero {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (g : X ⟶ Y) (t : U ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)
    (r : chain hcof hfib U Y d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q
        (FreeGeneratorCategories.identity (D C) (n + 1) X)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero U)) g t).append r) =
      OrdinaryBarChainFamily.family hcof hfib ((snoc hcof hfib P n j q g t).append r) := by
  unfold snoc
  rw [OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.interior_identity_at_zero (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) q _ t r

lemma small_trailing_identity {T : SSet.{v}}
    (k : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P n) {a : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a X)
    (t : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
      (snoc hcof hfib P n k q (FreeGeneratorCategories.identity (D C) (n + 1) X) t) =
      OrdinaryBarChainFamily.smallFamily hcof hfib q :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (trailing_identity hcof hfib P n k q t)

lemma small_leading_identity {T : SSet.{v}}
    (k : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P n) {b : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) X b)
    (t : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
      ((snoc hcof hfib P n k (.nil : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) X X)
        (FreeGeneratorCategories.identity (D C) (n + 1) X) t).append q) =
      OrdinaryBarChainFamily.smallFamily hcof hfib q :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (leading_identity hcof hfib P n k q t)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits
