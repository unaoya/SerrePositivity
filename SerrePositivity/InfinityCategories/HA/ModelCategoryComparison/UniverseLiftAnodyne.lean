module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneModelDetection
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne

/-!
分割で生成：docstring を書き直すこと
# 宇宙liftはモデル構造を仮定せずanodyne射を保つ

## 概要
宇宙liftはモデル構造を仮定せずanodyne射を保つ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0588][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0588
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Universe lift preserves anodyne extensions without model structures

Only the small horn small-object argument and colimit preservation are used.
The categorical localization comparison is consequently model independent.
-/

@[expose] public section
universe w v
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison

open HomotopicalAlgebra in
/-- All weak equivalences in the original small model become invertible after
lifting. Only the original small universe has a model structure. -/
lemma anodyneQ_map_isIso_of_weakEquivalence [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {X Y : SSet.{v}} (f : X ⟶ Y) (hf : weakEquivalences SSet.{v} f) :
    IsIso (_root_.SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.{max v w}.map (SSet.uliftFunctor.{w, v}.map f)) :=
  _root_.SerrePositivity.SimplicialModel.UniverseLift.anodyneQ_map_isIso_of_small f
    ((_root_.SerrePositivity.SimplicialModel.AnodyneHomotopy.weakEquivalences_iff_anodyneQ_isIso hcof hfib f).mp hf)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison
