module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ComponentClasses
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.BisimplicialCofibrancy
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.BisimplicialCofibrancy


/-!
# 二重単体的集合のReedy cofibrationの対角は単射となる

## 概要
二重単体的集合のReedy cofibrationの対角は単射となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
対角で評価した射の成分を計算し、単射性を各次数で確認する。
Reedy cofibrationに対する主張を既存の単射性の比較へ帰着する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0382][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0382
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Cofibrations under the actual bisimplicial diagonal

The diagonal preserves monomorphisms and Reedy cofibrations. Reedy
cofibrancy of all bisimplicial sets reduces weak-equivalence preservation
to proving the remaining Quillen condition. That condition is not assumed
as a completed diagonal theorem in this module.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.BisimplicialModel

/-- 二重単体的集合のReedy cofibrationの対角は単射となる。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
対角で評価した射の成分を計算し、単射性を各次数で確認する。
Reedy cofibrationに対する主張を既存の単射性の比較へ帰着する。
-/
lemma diagonal_map_mono {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B') [Mono f] :
    Mono (diagonal.map f) := by
  have : ∀ n, Mono ((diagonal.map f).app n) := by
    intro n
    exact inferInstanceAs (Mono ((f.app n).app n))
  exact NatTrans.mono_of_mono_app _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma diagonal_map_reedyCofibration {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}}
    (f : B ⟶ B') (hf : reedyLeft simplexOp (cofibrations SSet.{v}) f) :
    cofibrations SSet.{v} (diagonal.map f) := by
  have : ∀ n, Mono (f.app n) := by
    intro n
    change MorphismProperty.monomorphisms SSet.{v} (f.app n)
    rw [← hcof]
    exact cofibration_app simplexOp f hf n
  have : Mono f := NatTrans.mono_of_mono_app _
  rw [hcof]
  exact diagonal_map_mono f

include hcof in
/-- The formal reduction using actual Reedy cofibrancy. The missing Quillen
proof must be supplied before this becomes an unconditional diagonal theorem. -/
lemma diagonal_map_weakEquivalence_of_isLeftQuillen
    (hQ : let := simplexOpModelCategory SSet.{v}; Quillen.IsLeftQuillen diagonal.{v})
    {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B')
    (hf : ∀ n, weakEquivalences SSet.{v} (f.app n)) :
    weakEquivalences SSet.{v} (diagonal.map f) := by
  have hB := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.BisimplicialCofibrancy.isCofibrant hcof B
  have hB' := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.BisimplicialCofibrancy.isCofibrant hcof B'
  let := simplexOpModelCategory SSet.{v}
  have : Quillen.IsLeftQuillen diagonal.{v} := hQ
  have : IsCofibrant B := hB
  have : IsCofibrant B' := hB'
  have : WeakEquivalence f := ⟨hf⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant diagonal f)

end SerrePositivity.BisimplicialModel
