module

public import Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 通常の局所化圏の射集合を両変数に自然な離散単体的集合の図式にする

## 概要
通常の局所化圏の射集合を両変数に自然な離散単体的集合の図式にする。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0108][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0108
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The small ordinary localized Hom diagram on both original base variables

Local smallness comes from the source model category, without any simplicial
model structure. This discrete diagram records mapping classes, not RMap.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.LocalizedHomDiagram
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

abbrev value (b : Cᵒᵖ × C) : Type v := by
  letI : LocallySmall.{v} H := locallySmall_of_isLocalization Q
  exact Shrink.{v} (Q.obj b.1.unop ⟶ Q.obj b.2)

def equiv (b : Cᵒᵖ × C) : value Q b ≃ (Q.obj b.1.unop ⟶ Q.obj b.2) := by
  letI : LocallySmall.{v} H := locallySmall_of_isLocalization Q
  exact (equivShrink _).symm

def types : Cᵒᵖ × C ⥤ Type v where
  obj := value Q
  map {b c} f := ↾fun x => (equiv Q c).symm
    (Q.map f.1.unop ≫ equiv Q b x ≫ Q.map f.2)
  map_id b := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (equiv Q b).injective
    change equiv Q b ((equiv Q b).symm _) = equiv Q b x
    simp only [Equiv.apply_symm_apply, prod_id_fst, prod_id_snd,
      unop_id, Q.map_id, Category.id_comp,
      Category.comp_id]
  map_comp {a b c} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (equiv Q c).injective
    change equiv Q c ((equiv Q c).symm _) =
      equiv Q c ((equiv Q c).symm (Q.map g.1.unop ≫
        equiv Q b ((equiv Q b).symm (Q.map f.1.unop ≫ equiv Q a x ≫ Q.map f.2)) ≫
        Q.map g.2))
    simp only [Equiv.apply_symm_apply, prod_comp_fst, prod_comp_snd,
      unop_comp, Q.map_comp, Category.assoc]

lemma types_map {a b : Cᵒᵖ × C} (f : a ⟶ b) (x : value Q a) :
    equiv Q b ((types Q).map f x) = Q.map f.1.unop ≫ equiv Q a x ≫ Q.map f.2 :=
  (equiv Q b).apply_symm_apply _

/-- 通常の局所化圏の射集合を両変数に自然な離散単体的集合の図式にする。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
abbrev spaces : Cᵒᵖ × C ⥤ SSet.{v} := types Q ⋙ Functor.const SimplexCategoryᵒᵖ

end SerrePositivity.HomotopyFunctionComplex.LocalizedHomDiagram
