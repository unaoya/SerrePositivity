module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom

/-!
# 指定した値モデルで構成した関手的Kan置換は弱同値を保つ

## 概要
指定した値モデルで構成した関手的Kan置換は弱同値を保つ。
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
[棚卸し m0432][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0432
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A functorial Kan replacement built on the value side

The fixed boundary/horn generators supply functorial factorization in SSet.
No functorial factorization is required of a model category whose mapping
spaces will later be replaced. Product preservation is not asserted.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.ModelGeneration SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.SimplicialModel.KanReplacement
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- The actual value-model factorization, supplied by its proved generators. -/
def factorization : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations SSet.{v}) (fibrations SSet.{v}) := by
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{v} SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J :=
    simplicial_cofibrantlyGenerated hcof hfib
  have : (trivialCofibrations SSet.{v}).HasFunctorialFactorization (fibrations SSet.{v}) :=
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration
      SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J
  exact MorphismProperty.functorialFactorizationData _ _

abbrev functor : SSet.{v} ⥤ SSet.{v} := fibrantTarget (factorization hcof hfib)
abbrev unit : 𝟭 SSet.{v} ⟶ functor hcof hfib := fibrantTargetComparison (factorization hcof hfib)

lemma unit_cofibration (K : SSet.{v}) :
    cofibrations SSet.{v} ((unit hcof hfib).app K) :=
  ((factorization hcof hfib).hi (Arrow.mk (terminal.from K))).1

lemma unit_mono (K : SSet.{v}) : Mono ((unit hcof hfib).app K) := by
  have h := unit_cofibration hcof hfib K
  rw [hcof] at h
  exact h

lemma unit_weakEquivalence (K : SSet.{v}) :
    weakEquivalences SSet.{v} ((unit hcof hfib).app K) :=
  fibrantTargetComparison_weakEquivalence _ K

lemma isFibrant (K : SSet.{v}) : IsFibrant ((functor hcof hfib).obj K) :=
  fibrantTarget_isFibrant _ K

lemma kanComplex (K : SSet.{v}) : SSet.KanComplex ((functor hcof hfib).obj K) := by
  have := isFibrant hcof hfib K
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  rw [← hfib]
  exact mem_fibrations (terminal.from ((functor hcof hfib).obj K))

/-- 指定した値モデルで構成した関手的Kan置換は弱同値を保つ。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma map_weakEquivalence {K L : SSet.{v}} (f : K ⟶ L) (hf : weakEquivalences SSet.{v} f) :
    weakEquivalences SSet.{v} ((functor hcof hfib).map f) :=
  fibrantTarget_map_weakEquivalence _ f hf

include hfib in
/-- Transport canonical Kan fibrancy to the explicitly supplied value-model fibrations. -/
lemma isFibrant_of_kanComplex (K : SSet.{v}) [SSet.KanComplex K] : IsFibrant K := by
  apply (HomotopicalAlgebra.fibration_iff (terminal.from K)).mpr
  rw [hfib]
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp
    (inferInstanceAs (SSet.KanComplex K))

end SerrePositivity.SimplicialModel.KanReplacement
