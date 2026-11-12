module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionCenters
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveSmallFamilies

/-!
# 中断した任意モデル源への一般化：NerveMixedAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole-chain mixed actions with both moving center transports。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0129][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0129
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole-chain mixed actions with both moving center transports

Both original coherent systems are used without changing their chain
families. All simplex operators retain the actual prefix and tail maps.
-/

@[expose] public section
universe v u w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.NerveMixedAction
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (H : D ⥤ MixedResolutionCenters.Index C)
  (K : D ⥤ SSet.{v})
  (a : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.leftChoices C))
  (b : NerveMovingParameter.System.{w, v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.rightChoices C))

abbrev parameter {n : ℕ} (c : ComposableArrows D n) :=
  K.obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)
abbrev center {n : ℕ} (c : ComposableArrows D n) := H.obj (c.obj (Fin.last n))
abbrev input {n : ℕ} (c : ComposableArrows D n) :=
  (MixedResolutionCenters.input C).obj (op (center C H c))

def action {n : ℕ} (c : ComposableArrows D n) (t : parameter K c ⟶ input C H c) :
    parameter K c ⟶ (MixedResolutionCenters.kanOutput C hcof hfib).obj (center C H c) :=
  MixedResolutionCenters.kanAction C hcof hfib (center C H c)
    (NerveSmallFamilies.family K (H ⋙ MixedResolutionCenters.leftChoices C) a c)
    (NerveSmallFamilies.family K (H ⋙ MixedResolutionCenters.rightChoices C) b c) t

abbrev reindexChain {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) : ComposableArrows D m :=
  (SimplexCategory.toCat.map θ).toFunctor ⋙ c
abbrev operatorParameter {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  K.obj (c.obj 0) ◁ SSet.stdSimplex.{v}.map θ
abbrev prefixParameter {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  K.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) ▷
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk m)
abbrev tailMap {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  H.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))

lemma operator {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (t : parameter K c ⟶ input C H c) :
    operatorParameter K c θ ≫ action C hcof hfib H K a b c t =
      MixedResolutionCenters.kanAction C hcof hfib (center C H (reindexChain c θ))
        (prefixParameter K c θ ≫ NerveSmallFamilies.family K
          (H ⋙ MixedResolutionCenters.leftChoices C) a (reindexChain c θ))
        (prefixParameter K c θ ≫ NerveSmallFamilies.family K
          (H ⋙ MixedResolutionCenters.rightChoices C) b (reindexChain c θ))
        ((operatorParameter K c θ ≫ t) ≫ (MixedResolutionCenters.input C).map
          (tailMap C H c θ).op) ≫
        (MixedResolutionCenters.kanOutput C hcof hfib).map (tailMap C H c θ) := by
  change _ ≫ MixedResolutionCenters.kanAction _ _ _ _ _ _ _ = _
  rw [MixedResolutionCenters.kan_action_parameter,
    NerveSmallFamilies.family_naturality, NerveSmallFamilies.family_naturality]
  exact MixedResolutionCenters.kan_action_transport C hcof hfib (tailMap C H c θ) _ _ _

lemma operator_of_input {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (t : parameter K c ⟶ input C H c)
    (t' : parameter K (reindexChain c θ) ⟶ input C H (reindexChain c θ))
    (ht : (operatorParameter K c θ ≫ t) ≫ (MixedResolutionCenters.input C).map
      (tailMap C H c θ).op = prefixParameter K c θ ≫ t') :
    operatorParameter K c θ ≫ action C hcof hfib H K a b c t =
      (prefixParameter K c θ ≫ action C hcof hfib H K a b (reindexChain c θ) t') ≫
        (MixedResolutionCenters.kanOutput C hcof hfib).map (tailMap C H c θ) := by
  rw [operator, ht]
  exact congrArg (fun k => k ≫
    (MixedResolutionCenters.kanOutput C hcof hfib).map (tailMap C H c θ))
      (MixedResolutionCenters.kan_action_parameter C hcof hfib
        (center C H (reindexChain c θ)) (prefixParameter K c θ) _ _ t').symm

end SerrePositivity.HomotopyFunctionComplex.NerveMixedAction
