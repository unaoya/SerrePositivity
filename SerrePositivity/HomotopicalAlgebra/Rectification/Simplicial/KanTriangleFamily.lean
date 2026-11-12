module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanReplacement
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceCells

/-!
# 中断した任意モデル源への一般化：KanTriangleFamily

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Kan extensions of triangle families and relative reindexing comparisons。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0439][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0439
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Kan extensions of triangle families and relative reindexing comparisons

Parameter maps satisfy strict identity and composition laws. The separately
chosen extensions are compared by actual homotopies fixed on the whole
original triangle family. Their equality or strict naturality is not assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.KanTriangleFamily
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
  (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
  (hp : trivialFibrations SSet.{v} p)

abbrev parameter (I : Type v) : SSet.{v} :=
  (KanReplacement.functor hcof hfib).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj I)
abbrev inclusion (I : Type v) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj I ⟶ parameter hcof hfib I :=
  (KanReplacement.unit hcof hfib).app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj I)

local instance (I : Type v) : Mono (inclusion hcof hfib I) := KanReplacement.unit_mono _ _ _

abbrev reindex {I J : Type v} (α : I → J) :
    parameter hcof hfib I ⟶ parameter hcof hfib J :=
  (KanReplacement.functor hcof hfib).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex α)

@[reassoc]
lemma inclusion_reindex {I J : Type v} (α : I → J) :
    inclusion hcof hfib I ≫ reindex hcof hfib α =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex α ≫ inclusion hcof hfib J :=
  ((KanReplacement.unit hcof hfib).naturality (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex α)).symm

lemma reindex_id (I : Type v) : reindex hcof hfib (id : I → I) = 𝟙 _ := by
  rw [reindex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex_id, CategoryTheory.Functor.map_id]

lemma reindex_comp {I J K : Type v} (α : I → J) (β : J → K) :
    reindex hcof hfib α ≫ reindex hcof hfib β = reindex hcof hfib (β ∘ α) := by
  rw [reindex, reindex, ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex_comp]

variable {I : Type v}
  (d : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ RelativeChoiceSpace.obj i b)
  (f : I → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ RelativeChoiceSpace.obj i b))
  (hf : ∀ k, SSet.stdSimplex.δ (1 : Fin 3) ≫ f k = d)

def extension : parameter hcof hfib I ⟶ RelativeChoiceSpace.obj i b :=
  RelativeChoiceCells.assemble hcof hfib i b p hp (inclusion hcof hfib I)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d f hf) (fun _ _ => none)

@[reassoc]
lemma extension_initial : inclusion hcof hfib I ≫ extension hcof hfib i b p hp d f hf =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d f hf := RelativeChoiceCells.assemble_initial _ _ _ _ _ _ _ _ _

@[reassoc]
lemma extension_triangle (k : I) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle I k ≫ inclusion hcof hfib I) ≫
      extension hcof hfib i b p hp d f hf = f k := by
  rw [Category.assoc, extension_initial, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle_desc]

variable {J : Type v} (α : J → I)

abbrev restricted : parameter hcof hfib J ⟶ RelativeChoiceSpace.obj i b :=
  extension hcof hfib i b p hp d (fun j => f (α j)) (fun j => hf (α j))

abbrev transported : parameter hcof hfib J ⟶ RelativeChoiceSpace.obj i b :=
  reindex hcof hfib α ≫ extension hcof hfib i b p hp d f hf

@[reassoc]
lemma transported_initial : inclusion hcof hfib J ≫ transported hcof hfib i b p hp d f hf α =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d (fun j => f (α j)) (fun j => hf (α j)) := by
  rw [transported, ← Category.assoc, inclusion_reindex, Category.assoc, extension_initial,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.desc_reindex]

/-- The comparison fixes every whole original triangle, including repeated selections. -/
def reindexHomotopy : RelativeChoiceSpace.FixedBoundaryHomotopy (inclusion hcof hfib J)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc d (fun j => f (α j)) (fun j => hf (α j)))
    (restricted hcof hfib i b p hp d f hf α) (transported hcof hfib i b p hp d f hf α) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.nonempty_fixedBoundaryHomotopy hcof hfib _ _
    (RelativeChoiceSpace.projection i b)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.projection_trivialFibration hcof hfib i b p hp) _ _
    (extension_initial hcof hfib i b p hp d (fun j => f (α j)) (fun j => hf (α j)))
    (transported_initial hcof hfib i b p hp d f hf α))

end SerrePositivity.SimplicialModel.KanTriangleFamily
