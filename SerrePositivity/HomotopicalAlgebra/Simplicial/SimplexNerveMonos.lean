module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 単体圏のnerveを取る関手は単射を保つ

## 概要
単体圏のnerveを取る関手は単射を保つ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0566][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0566
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual simplex-nerve functor preserves monomorphisms

The index chain is unchanged and the original first label is sent by
the original injective component. No model structure is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.SimplexNerve
variable {X Y : SSet.{v}} (f : X ⟶ Y) [Mono f]

lemma degreeLabels_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((degreeLabels n).map f) := by
  change Function.Injective (Sigma.map (fun δ : Chains n => δ)
    (fun δ x => f.app (δ.obj 0) x))
  exact Function.Injective.sigma_map Function.injective_id
    (fun δ => (mono_iff_injective (f.app (δ.obj 0))).mp inferInstance)

/-- 単体圏のnerveを取る関手は単射を保つ。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。
-/
lemma map_injective (n : SimplexCategoryᵒᵖ) : Function.Injective ((functor.map f).app n) := by
  intro c d h
  apply (chainEquiv X n).injective
  apply degreeLabels_injective f n
  exact congrArg (chainEquiv Y n) h

instance map_mono : Mono (functor.map f) :=
  (NatTrans.mono_iff_mono_app _).mpr (fun n =>
    (mono_iff_injective _).mpr (map_injective f n))

instance preservesMonomorphisms : functor.{v}.PreservesMonomorphisms where
  preserves _ _ := inferInstance

end SerrePositivity.SimplicialModel.SimplexNerve
