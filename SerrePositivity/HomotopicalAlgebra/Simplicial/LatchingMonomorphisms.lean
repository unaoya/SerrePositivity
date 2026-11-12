module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Types.Monomorphisms
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingDegeneracies
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.LatchingDegeneracies

/-!
# 単体的集合のlatching比較射は単射となる

## 概要
単体的集合のlatching比較射は単射となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0447][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0447
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Simplicial latching comparisons are monomorphisms

The latching cocone embeds its colimit into the set of simplices. Equality
of two images is witnessed by an actual common degeneracy refinement, not
by a presumed splitting of a simplicial object in an arbitrary category.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialLatching

/-- 単体的集合のlatching比較射は単射となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma comparison_mono (X : SSet.{v}) (j : SimplexCategoryᵒᵖ) :
    Mono ((latchingComparison simplexOp j).app X) := by
  apply (mono_iff_injective _).mpr
  intro x y h
  obtain ⟨a, xa, rfl⟩ := Types.jointly_surjective' x
  obtain ⟨b, yb, rfl⟩ := Types.jointly_surjective' y
  have ha (i : LatchingIndex simplexOp j) (z : X.obj i.obj.left) :
      (latchingComparison simplexOp j).app X (colimit.ι (latchingSource simplexOp j ⋙ X) i z) =
        X.map i.obj.hom z :=
    congrArg (fun k => k z) (colimit.ι_desc (latchingCocone simplexOp X j) i)
  have h' := (ha a xa).symm.trans (h.trans (ha b yb))
  obtain ⟨r, u, w, z, hzx, hzy⟩ := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.common_refinement X a b xa yb h'
  have hu := congrArg (fun k => k z) (colimit.w (latchingSource simplexOp j ⋙ X) u)
  have hw := congrArg (fun k => k z) (colimit.w (latchingSource simplexOp j ⋙ X) w)
  change colimit.ι (latchingSource simplexOp j ⋙ X) a (X.map u.hom.left z) =
    colimit.ι (latchingSource simplexOp j ⋙ X) r z at hu
  change colimit.ι (latchingSource simplexOp j ⋙ X) b (X.map w.hom.left z) =
    colimit.ι (latchingSource simplexOp j ⋙ X) r z at hw
  rw [hzx] at hu
  rw [hzy] at hw
  exact hu.trans hw.symm

end SerrePositivity.SimplicialLatching
