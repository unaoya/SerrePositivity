module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples

/-!
# 中断した任意モデル源への一般化：VertexTuplesFunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Ordered tuple spaces and strict vertex inclusions as actual functors。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0605][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0605
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Ordered tuple spaces and strict vertex inclusions as actual functors
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

def tupleFunctor : Type v ⥤ SSet.{v} where
  obj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.obj
  map f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map f

def vertexFunctor : Type v ⥤ SSet.{v} where
  obj := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.vertices
  map f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap f

def inclusionNatTrans : vertexFunctor ⟶ tupleFunctor where
  app := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion
  naturality {_ _} f := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion_map f).symm

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
