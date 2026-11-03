module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs

/-!
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

namespace SerrePositivity.SimplicialLatching

lemma common_nondegenerate (X : SSet.{v}) {n m l : ℕ}
    (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m) [Epi f]
    (g : SimplexCategory.mk n ⟶ SimplexCategory.mk l) [Epi g]
    (x : X.obj (Opposite.op (SimplexCategory.mk m)))
    (y : X.obj (Opposite.op (SimplexCategory.mk l)))
    (h : X.map f.op x = X.map g.op y) :
    ∃ (k : ℕ) (a : SimplexCategory.mk m ⟶ SimplexCategory.mk k)
      (b : SimplexCategory.mk l ⟶ SimplexCategory.mk k),
      Epi a ∧ Epi b ∧ ∃ z : X.nonDegenerate k,
        x = X.map a.op z ∧ y = X.map b.op z ∧ f ≫ a = g ≫ b := by
  obtain ⟨k, a, ha, z, hx⟩ := X.exists_nonDegenerate x
  obtain ⟨k', b, hb, z', hy⟩ := X.exists_nonDegenerate y
  have : Epi a := ha
  have : Epi b := hb
  have hx' : X.map f.op x = X.map (f ≫ a).op z := by
    rw [hx]
    exact congrArg (fun q => q z.val) (X.map_comp a.op f.op).symm
  have hy' : X.map f.op x = X.map (g ≫ b).op z' := by
    rw [h, hy]
    exact congrArg (fun q => q z'.val) (X.map_comp b.op g.op).symm
  have hdim := X.unique_nonDegenerate_dim _ (f ≫ a) z hx' (g ≫ b) z' hy'
  subst k'
  have hz := X.unique_nonDegenerate_simplex _ (f ≫ a) z hx' (g ≫ b) z' hy'
  subst z'
  exact ⟨k, a, b, ha, hb, z, hx, hy,
    X.unique_nonDegenerate_map _ (f ≫ a) z hx' (g ≫ b) z hy'⟩

end SerrePositivity.SimplicialLatching
