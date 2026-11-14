module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.VertexTuples

/-!
# 圏のnerveにその頂点部分単体集合を含める射を構成する

## 概要
圏のnerveにその頂点部分単体集合を含める射を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
離散な対象の族からnerveへの写像を各次数で明示する。
像の部分単体集合と包含を使い、各頂点の評価を確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0017][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/archive/k-theory-generalization-inventory.md#m0017
[plan]: ../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual vertex subcomplex of a category nerve
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.NerveVertices
variable (C : Type u) [Category.{v} C]

abbrev vertices : SSet.{max u v} := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.vertices (ULift.{v} C)

/-- 圏のnerveにその頂点部分単体集合を含める射を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
離散な対象の族からnerveへの写像を各次数で明示する。
像の部分単体集合と包含を使い、各頂点の評価を確認する。
-/
def inclusion : vertices C ⟶ nerve C where
  app _ := ↾fun x => (Functor.const _).obj x.down
  naturality {_ _} _ := rfl

instance : Mono (inclusion C) := by
  have : ∀ n, Mono ((inclusion C).app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (fun x y h =>
      ULift.ext (Functor.congr_obj h 0))
  exact NatTrans.mono_of_mono_app _

@[reassoc]
lemma vertex_inclusion (a : C) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.vertex (⟨a⟩ : ULift.{v} C) ≫ inclusion C =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₀ a) := rfl

end SerrePositivity.NerveVertices
