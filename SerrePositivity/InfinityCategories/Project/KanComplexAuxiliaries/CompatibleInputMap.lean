module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion

/-!
# 中断した任意モデル源への一般化：CompatibleInputMap

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：A map of input families induces a map on their small unions。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0373][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0373
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A map of input families induces a map on their small unions
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputMap
variable {J : Type u} {B D : SSet.{v}} (S T : J → SSet.{v})
  (b : ∀ j, S j ⟶ B) (c : ∀ j, T j ⟶ D)
  (q : B ⟶ D) (t : ∀ j, S j ⟶ T j) (h : ∀ j, b j ≫ q = t j ≫ c j)

def map : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.inputs S b).toSSet ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.inputs T c).toSSet where
  app m := ↾fun x => ⟨q.app m x.val, by
    obtain ⟨j, y, hy⟩ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.mem_inputs S b m x.val).mp x.property
    apply (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.mem_inputs T c m _).mpr
    refine ⟨j, (t j).app m y, ?_⟩
    exact (types_congr_hom (congr_app (h j) m) y).symm.trans (congrArg (q.app m) hy)⟩
  naturality {m n} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact types_congr_hom (q.naturality θ) x.val

lemma map_inclusion : map S T b c q t h ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.inputs T c).ι =
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.inputs S b).ι ≫ q := rfl

lemma toInputs_map (j : J) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs S b j ≫ map S T b c q t h =
    t j ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs T c j := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.inputs T c).ι).mp
  rw [Category.assoc, map_inclusion, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs_inclusion, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.toInputs_inclusion]
  exact h j

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputMap
