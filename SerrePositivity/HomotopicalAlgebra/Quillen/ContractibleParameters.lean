module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 可縮かつfibrantなパラメータを付加するグラフ射が弱同値となる

## 概要
可縮かつfibrantなパラメータを付加するグラフ射が弱同値となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
終対象への自明fibrationを直積のpullback表示に沿って引き戻す。
射影の弱同値性と合成の式から、グラフ射の弱同値性を導く。

## 規約と注意
終対象への射が自明fibrationである条件を、可縮fibrantなパラメータの意味として使う。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0336][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0336
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Adding contractible fibrant parameters preserves weak equivalences

All statements use actual products and their projections. No enrichment
or functorial factorization of the model category is needed.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen.ContractibleParameters
variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasBinaryProducts C]
  {S R Z T V : C} (hZ : IsTerminal Z)
include hZ

lemma projection_trivialFibration (p : S ⟶ Z) (hp : trivialFibrations C p) (V : C) :
    trivialFibrations C (prod.snd : S ⨯ V ⟶ V) := by
  have hp' : trivialFibrations C (hZ.from S) := (hZ.hom_ext p (hZ.from S)) ▸ hp
  exact (trivialFibrations C).of_isPullback
    (IsPullback.of_is_product (prodIsProd S V) hZ) hp'

lemma double_projection_trivialFibration (p : S ⟶ Z) (q : R ⟶ Z)
    (hp : trivialFibrations C p) (hq : trivialFibrations C q) (V : C) :
    trivialFibrations C ((prod.snd : S ⨯ (R ⨯ V) ⟶ R ⨯ V) ≫ prod.snd) :=
  (trivialFibrations C).comp_mem _ _
    (projection_trivialFibration hZ p hp (R ⨯ V)) (projection_trivialFibration hZ q hq V)

/-- 可縮かつfibrantなパラメータを付加するグラフ射が弱同値となる。

終対象への射が自明fibrationである条件を、可縮fibrantなパラメータの意味として使う。
終対象への自明fibrationを直積のpullback表示に沿って引き戻す。
射影の弱同値性と合成の式から、グラフ射の弱同値性を導く。
-/
lemma graph_weakEquivalence (p : S ⟶ Z) (q : R ⟶ Z)
    (hp : trivialFibrations C p) (hq : trivialFibrations C q)
    (s : T ⟶ S) (r : T ⟶ R) (t : T ⟶ V) (ht : weakEquivalences C t) :
    weakEquivalences C (prod.lift s (prod.lift r t)) := by
  have hπ := double_projection_trivialFibration hZ p q hp hq V
  apply (weakEquivalences C).of_postcomp _ _ hπ.2
  simpa only [← Category.assoc, prod.lift_snd] using ht

end SerrePositivity.Quillen.ContractibleParameters
