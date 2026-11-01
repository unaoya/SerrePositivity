module

public import SerrePositivity.HomotopicalAlgebra.Replacement.FibrantCategory
public import Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# 同じ基底射を覆うfibrant置換間の比較は局所化後に等しくなる

## 概要
同じ基底射を覆うfibrant置換間の比較は局所化後に等しくなる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0338][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0338
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Homotopical target functors ignore replacement comparisons over the same base map
-/

@[expose] public section
universe v u vH uH vD uD
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.ModelReplacement.FibrantReplacementObject
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

/-- 同じ基底射を覆うfibrant置換間の比較は局所化後に等しくなる。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma localized_map_eq_of_base_eq {X Y : FibrantReplacementObject C} (f g : X ⟶ Y)
    (h : f.base = g.base) : Q.map f.map = Q.map g.map := by
  have : IsIso (Q.map X.inclusion) :=
    Localization.inverts Q (weakEquivalences C) _ X.trivial.2
  apply (cancel_epi (Q.map X.inclusion)).mp
  rw [← Q.map_comp, ← Q.map_comp, f.under, g.under, h]

variable {D : Type uD} [Category.{vD} D] (F : FibrantObject C ⥤ D)
  (hF : (weakEquivalences (FibrantObject C)).IsInvertedBy F)

include Q hF in
/-- The equality is in D itself when F already inverts weak equivalences. -/
lemma homotopical_map_eq_of_base_eq {X Y : FibrantReplacementObject C} (f g : X ⟶ Y)
    (h : f.base = g.base) :
    F.map ((fibrantTargets (C := C)).map f) = F.map ((fibrantTargets (C := C)).map g) := by
  let G := Localization.lift F hF (FibrantObject.ι ⋙ Q)
  let e : (FibrantObject.ι ⋙ Q) ⋙ G ≅ F :=
    Localization.fac F hF (FibrantObject.ι ⋙ Q)
  have hf := e.hom.naturality ((fibrantTargets (C := C)).map f)
  have hg := e.hom.naturality ((fibrantTargets (C := C)).map g)
  apply (cancel_epi (e.hom.app ((fibrantTargets (C := C)).obj X))).mp
  exact hf.symm.trans ((congrArg (fun k => G.map k ≫
    e.hom.app ((fibrantTargets (C := C)).obj Y))
      (localized_map_eq_of_base_eq Q f g h)).trans hg)

end SerrePositivity.ModelReplacement.FibrantReplacementObject
