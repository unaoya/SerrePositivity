module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleBook

/-!
# 中断した任意モデル源への一般化：TriangleBookMaps

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Strict reindexing of triangles with a shared edge。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0585][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0585
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Strict reindexing of triangles with a shared edge
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps

lemma hom_ext {I : Type v} {Q : SSet.{v}} {f g : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj I ⟶ Q}
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle I i ≫ f = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle I i ≫ g)
    (hd : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge I ≫ f = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge I ≫ g) : f = g := by
  apply pushout.hom_ext
  · apply Sigma.hom_ext
    intro i
    exact (Category.assoc _ _ _).symm.trans ((h i).trans (Category.assoc _ _ _))
  · exact hd

def reindex {I J : Type v} (α : I → J) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj I ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj J :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge J) (fun i => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle J (α i)) (fun i => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle_sharedEdge J (α i))

@[reassoc (attr := simp)]
lemma triangle_reindex {I J : Type v} (α : I → J) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle I i ≫ reindex α = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle J (α i) := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle_desc _ _ _ i

@[reassoc (attr := simp)]
lemma sharedEdge_reindex {I J : Type v} (α : I → J) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge I ≫ reindex α = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge J := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge_desc _ _ _

lemma reindex_id (I : Type v) : reindex (id : I → I) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj I) := by
  apply hom_ext
  · intro i
    exact (triangle_reindex id i).trans (Category.comp_id _).symm
  · exact (sharedEdge_reindex id).trans (Category.comp_id _).symm

lemma reindex_comp {I J K : Type v} (α : I → J) (β : J → K) :
    reindex α ≫ reindex β = reindex (β ∘ α) := by
  apply hom_ext
  · intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ reindex β) (triangle_reindex α i)).trans
        ((triangle_reindex β (α i)).trans (triangle_reindex (β ∘ α) i).symm))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ reindex β) (sharedEdge_reindex α)).trans
        ((sharedEdge_reindex β).trans (sharedEdge_reindex (β ∘ α)).symm))

lemma desc_reindex {I J : Type v} {Q : SSet.{v}} (α : I → J)
    (d : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ Q)
    (f : J → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ Q))
    (hf : ∀ j, SSet.stdSimplex.δ (1 : Fin 3) ≫ f j = d) :
    reindex α ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d f hf = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d (fun i => f (α i)) (fun i => hf (α i)) := by
  apply hom_ext
  · intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d f hf) (triangle_reindex α i)).trans
        ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle_desc d f hf (α i)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle_desc d (fun i => f (α i)) (fun i => hf (α i)) i).symm))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d f hf) (sharedEdge_reindex α)).trans
        ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge_desc d f hf).trans
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge_desc d (fun i => f (α i)) (fun i => hf (α i))).symm))

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps
