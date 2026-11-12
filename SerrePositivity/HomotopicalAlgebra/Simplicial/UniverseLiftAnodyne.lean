module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClassFunctor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift

/-!
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

namespace SerrePositivity.SimplicialModel.UniverseLift

lemma hornGenerator_anodyne_map : SSet.modelCategoryQuillen.J.{v} ≤
    SSet.anodyneExtensions.{max v w}.inverseImage SSet.uliftFunctor.{w, v} := by
  intro X Y f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact (SSet.anodyneExtensions.arrow_iso_iff (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornArrowIso.{w, v} (n + 1) i)).mpr
    (SSet.anodyneExtensions.horn_ι i)

/- 旧宣言の技術注記：
The larger universe needs no model category structure.
-/
/-- 宇宙liftはモデル構造を仮定せずanodyne射を保つ。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
lemma anodyne_map : SSet.anodyneExtensions.{v} ≤
    SSet.anodyneExtensions.{max v w}.inverseImage SSet.uliftFunctor.{w, v} := by
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  exact ModelGeneration.generatedLeft_map SSet.uliftFunctor SSet.anodyneExtensions
    SSet.modelCategoryQuillen.J hornGenerator_anodyne_map

open AnodyneHomotopy in
lemma anodyneQ_lift_inverts : SSet.anodyneExtensions.{v}.IsInvertedBy
    (SSet.uliftFunctor.{w, v} ⋙ anodyneQ.{max v w}) := by
  intro X Y f hf
  exact Localization.inverts anodyneQ SSet.anodyneExtensions _ (anodyne_map f hf)

open AnodyneHomotopy in
lemma anodyneQ_map_isIso_of_small {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (anodyneQ.{v}.map f)) :
    IsIso (anodyneQ.{max v w}.map (SSet.uliftFunctor.{w, v}.map f)) :=
  map_isIso_of_anodyneQ_isIso (SSet.uliftFunctor ⋙ anodyneQ) anodyneQ_lift_inverts f hf

end SerrePositivity.SimplicialModel.UniverseLift
