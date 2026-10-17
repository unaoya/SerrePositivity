module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.AnchoredChain
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# 中断した任意モデル源への一般化：AnchoredChainSimplicial

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual simplicial set of chains with fixed external endpoints。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0004][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0004
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual simplicial set of chains with fixed external endpoints

All ordinal operators act by reindexing the internal diagram and composing
the surrounding arrows. The object and Hom universes remain independent;
the set of chains uses their maximum, as it contains internal objects.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.AnchoredChain
variable {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V)

def simplicial : SSet.{max u v} where
  obj n := AnchoredChain g n.unop.len
  map θ := ↾fun c => reindex c θ.unop.toOrderHom
  map_id _ := by
    ext c
    exact reindex_id c
  map_comp θ φ := by
    ext c
    exact (reindex_comp c θ.unop.toOrderHom φ.unop.toOrderHom).symm

end SerrePositivity.AnchoredChain
