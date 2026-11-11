module
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LatchingDegeneracies


/-!
分割で生成：docstring を書き直すこと
# 二つの退化表示に共通の細分を構成する

## 概要
二つの退化表示に共通の細分を構成する。
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
[棚卸し m0446][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0446
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Common refinements of degeneracy presentations

Eilenberg--Zilber uniqueness gives a common lower-dimensional simplex for
any two degeneracy presentations with the same image. This is the concrete
input for the injectivity of simplicial latching comparisons.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72

/-- A proper epimorphism determines an actual latching-index object. -/
def ofEpi {n m : SimplexCategory} (f : n ⟶ m)
    [Epi f] (hlt : m.len < n.len) : LatchingIndex simplexOp (Opposite.op n) :=
  ⟨Over.mk f.op, inferInstanceAs (Epi f), by
    have hid : MorphismProperty.identities SimplexCategoryᵒᵖ ≤
        fun i j _ => i.unop.len = j.unop.len := by
      rintro _ _ _ ⟨i⟩
      rfl
    intro h
    exact (Nat.ne_of_lt hlt) (hid _ h)⟩

/- 旧宣言の技術注記：
Equal images in a simplicial latching cocone have an actual common refinement.
-/
/-- 二つの退化表示に共通の細分を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma common_refinement (X : SSet.{v}) {j : SimplexCategoryᵒᵖ}
    (a b : LatchingIndex simplexOp j) (x : X.obj a.obj.left) (y : X.obj b.obj.left)
    (h : X.map a.obj.hom x = X.map b.obj.hom y) :
    ∃ (r : LatchingIndex simplexOp j) (u : r ⟶ a) (w : r ⟶ b) (z : X.obj r.obj.left),
      X.map u.hom.left z = x ∧ X.map w.hom.left z = y := by
  have : Epi a.obj.hom.unop := a.property.1
  have : Epi b.obj.hom.unop := b.property.1
  obtain ⟨k, u, w, hu, hw, z, hx, hy, he⟩ :=
    _root_.SerrePositivity.SimplicialLatching.common_nondegenerate X a.obj.hom.unop b.obj.hom.unop x y h
  have : Epi u := hu
  have : Epi w := hw
  let r := ofEpi (a.obj.hom.unop ≫ u)
    (lt_of_le_of_lt (SimplexCategory.len_le_of_epi u) (latching_degree_lt simplexOp a))
  let ra : r ⟶ a := ObjectProperty.homMk (Over.homMk u.op (by rfl))
  let rb : r ⟶ b := ObjectProperty.homMk (Over.homMk w.op (by
    change (b.obj.hom.unop ≫ w).op = (a.obj.hom.unop ≫ u).op
    exact congrArg Quiver.Hom.op he.symm))
  exact ⟨r, ra, rb, z.val, hx.symm, hy.symm⟩

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
