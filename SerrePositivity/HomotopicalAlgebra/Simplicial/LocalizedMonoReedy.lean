module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ClosedObjectwise
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# Reedy局所化単射をReedy単射かつ各成分の局所化同値として特徴付ける

## 概要
Reedy局所化単射をReedy単射かつ各成分の局所化同値として特徴付ける。
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
[棚卸し m0448][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0448
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reedy localized mono equivalences are precisely Reedy monos with localized components
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.LocalizedMonoReedy
open KanTestLiftingClass

local instance : IsLocallyPresentable.{v} SSet.{v} :=
  Smith.AccessibleLimits.functorCategory_isLocallyPresentable
    (C := Type v) SimplexCategoryᵒᵖ

instance multiplicative : localizedMonos.{v}.IsMultiplicative := by
  rw [localizedMonos_eq]
  infer_instance

instance retracts : localizedMonos.{v}.IsStableUnderRetracts := by
  rw [localizedMonos_eq]
  infer_instance

instance coproducts : localizedMonos.{v}.IsStableUnderCoproducts.{v} := by
  constructor
  intro I
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf
  have : ∀ i, Mono (f i) := fun i => (hf i).1
  have hl := KanLocalizedCoproducts.coproduct_mem rightTests.llp I f
    (fun i => localizedMono_le_llp _ (hf i))
  exact ⟨inferInstance, localized_isIso_of_llp _ hl⟩

instance cobaseChange : localizedMonos.{v}.IsStableUnderCobaseChange := by
  rw [localizedMonos_eq]
  infer_instance

abbrev equivalences : MorphismProperty SSet.{v} :=
  (MorphismProperty.isomorphisms _).inverseImage AnodyneHomotopy.anodyneQ

lemma localizedMonos_inf : localizedMonos.{v} =
    MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences := rfl

/-- Reedy局所化単射をReedy単射かつ各成分の局所化同値として特徴付ける。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma reedy_iff {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B) :
    reedyLeft simplexOp localizedMonos f ↔
      reedyLeft simplexOp (MorphismProperty.monomorphisms _) f ∧
        ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n)) := by
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsMultiplicative :=
    multiplicative
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsStableUnderRetracts := retracts
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsStableUnderCoproducts.{v} :=
    coproducts
  have : (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences).IsStableUnderCobaseChange :=
    cobaseChange
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{v}
      (MorphismProperty.monomorphisms SSet.{v} ⊓ equivalences) := KanLocalizedTransfinite.stable
  rw [localizedMonos_inf]
  exact reedyLeft_inf_iff.{v} simplexOp f (MorphismProperty.monomorphisms _) equivalences

end SerrePositivity.SimplicialModel.LocalizedMonoReedy
