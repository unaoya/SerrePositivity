module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PostChainKanParameter
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanTriangleFamily

/-!
# 中断した任意モデル源への一般化：PostChainReindexing

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Selecting and repeating cut comparisons of a fixed finite chain。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0258][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0258
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Selecting and repeating cut comparisons of a fixed finite chain

Arbitrary small index maps select or repeat the actual existing cut
triangles. The original full-cut extension is recovered definitionally.
Reindexing comparisons fix the whole selected triangle family.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.PostChainReindexing
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {n : ℕ} (F : Fin (n + 1) ⥤ ResolutionObject C)
  (X : ResolutionObject C) (f : X.base ⟶ (F.obj 0).base)
  {I : Type v} (cuts : I → Fin (n + 1))

abbrev comparison := KanTriangleFamily.extension hcof hfib (vertexInclusion X (F.obj 0) f)
  (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
  (ResolutionLiftSpace.projection X (F.obj (Fin.last n)) (f ≫ (PostCompositionChain.total F).base))
  (ResolutionLiftSpace.projection_trivialFibration hcof X (F.obj (Fin.last n))
    (f ≫ (PostCompositionChain.total F).base))
  (postEdge hcof hfib X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
  (fun i => PostCompositionChain.cutTriangle hcof hfib F X f (cuts i))
  (fun i => PostCompositionChain.cutTriangle_direct hcof hfib F X f (cuts i))

lemma full_comparison : comparison hcof hfib F X f (fun i : ULift.{v} (Fin (n + 1)) => i.down) =
    PostChainKanParameter.comparison hcof hfib F X f := rfl

@[reassoc]
lemma comparison_cut (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle I i ≫ KanTriangleFamily.inclusion hcof hfib I) ≫
      comparison hcof hfib F X f cuts = PostCompositionChain.cutTriangle hcof hfib F X f (cuts i) :=
  KanTriangleFamily.extension_triangle _ _ _ _ _ _ _ _ _ i

abbrev reindexHomotopy {J : Type v} (α : J → I) :=
  KanTriangleFamily.reindexHomotopy hcof hfib (vertexInclusion X (F.obj 0) f)
    (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
    (ResolutionLiftSpace.projection X (F.obj (Fin.last n))
      (f ≫ (PostCompositionChain.total F).base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X (F.obj (Fin.last n))
      (f ≫ (PostCompositionChain.total F).base))
    (postEdge hcof hfib X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
    (fun i => PostCompositionChain.cutTriangle hcof hfib F X f (cuts i))
    (fun i => PostCompositionChain.cutTriangle_direct hcof hfib F X f (cuts i)) α

end SerrePositivity.HomotopyFunctionComplex.PostChainReindexing
