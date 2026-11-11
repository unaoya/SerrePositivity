module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# 中断した任意モデル源への一般化：TriangleBook

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：A family of triangles with one shared edge。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0584][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0584
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A family of triangles with one shared edge

The parameter is the actual pushout identifying the 02 edge of all triangles.
Its maps are assembled from triangles with the same specified 02 edge.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook

variable (I : Type v)

abbrev edges : SSet.{v} := ∐ fun (_ : I) =>
  SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)

abbrev triangles : SSet.{v} := ∐ fun (_ : I) =>
  SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2)

abbrev attach : edges I ⟶ triangles I := Limits.Sigma.map fun _ => SSet.stdSimplex.δ (1 : Fin 3)
abbrev fold : edges I ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) :=
  Sigma.desc fun _ => 𝟙 _
abbrev obj : SSet.{v} := pushout (attach I) (fold I)

abbrev triangle (i : I) : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ obj I :=
  Sigma.ι (fun (_ : I) => SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2)) i ≫
    pushout.inl (attach I) (fold I)

abbrev sharedEdge : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ obj I :=
  pushout.inr (attach I) (fold I)

@[reassoc]
lemma triangle_sharedEdge (i : I) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle I i = sharedEdge I := by
  have h := congrArg (fun q =>
    Sigma.ι (fun (_ : I) => SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)) i ≫ q)
      (pushout.condition (f := attach I) (g := fold I))
  simpa [attach, fold, Category.assoc] using h

variable {I} {Q : SSet.{v}}
  (d : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ Q)
  (f : I → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ Q))
  (hf : ∀ i, SSet.stdSimplex.δ (1 : Fin 3) ≫ f i = d)

include hf in
lemma compatible : attach I ≫ Sigma.desc f = fold I ≫ d := by
  apply Sigma.hom_ext
  intro i
  simpa [attach, fold, Category.assoc] using hf i

def desc : obj I ⟶ Q := pushout.desc (Sigma.desc f) d (compatible d f hf)

@[reassoc]
lemma triangle_desc (i : I) : triangle I i ≫ desc d f hf = f i := by
  rw [triangle, Category.assoc, desc, pushout.inl_desc, Sigma.ι_comp_desc]

@[reassoc]
lemma sharedEdge_desc : sharedEdge I ≫ desc d f hf = d := pushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook
