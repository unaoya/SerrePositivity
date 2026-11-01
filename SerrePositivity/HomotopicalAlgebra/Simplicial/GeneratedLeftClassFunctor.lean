module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass

/-!
# 余極限を保つ関手が生成射上で左クラスを保てば生成された左クラス全体を保つ

## 概要
余極限を保つ関手が生成射上で左クラスを保てば生成された左クラス全体を保つ。
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
[棚卸し m0046][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0046
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Preservation of generated left classes by colimit preserving functors

The target only carries a morphism property closed under the four cell operations.
No model structure or adjoint on the target is required.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.ModelGeneration
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (W : MorphismProperty D)

lemma inverseImage_colimitsOfShape (J : Type*) [Category* J]
    [PreservesColimitsOfShape J F] [W.IsStableUnderColimitsOfShape J] :
    (W.inverseImage F).IsStableUnderColimitsOfShape J where
  condition X Y c d hc hd α hα f hf := by
    apply MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := W) (X ⋙ F) (Y ⋙ F) (F.mapCocone c) (F.mapCocone d)
      (isColimitOfPreserves F hc) (isColimitOfPreserves F hd)
      (Functor.whiskerRight α F) hα (F.map f)
    intro j
    exact (F.map_comp _ _).symm.trans ((congrArg F.map (hf j)).trans (F.map_comp _ _))

lemma inverseImage_cobaseChange [PreservesColimitsOfShape WalkingSpan F]
    [W.IsStableUnderCobaseChange] : (W.inverseImage F).IsStableUnderCobaseChange where
  of_isPushout sq hf := MorphismProperty.of_isPushout (P := W) (sq.map F) hf

/- 旧宣言の技術注記：
Small colimits and preservation of generating arrows suffice to preserve
the generated left class, with no lifting property imposed on the target.
-/
/-- 余極限を保つ関手が生成射上で左クラスを保てば生成された左クラス全体を保つ。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma generatedLeft_map (I : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    [PreservesColimitsOfSize.{w, w} F] [PreservesColimitsOfShape WalkingSpan F]
    [W.IsStableUnderRetracts] [W.IsStableUnderCobaseChange]
    [W.IsStableUnderCoproducts.{w}] [W.IsStableUnderTransfiniteComposition.{w}]
    (hI : I ≤ W.inverseImage F) : I.rlp.llp ≤ W.inverseImage F := by
  let : (W.inverseImage F).IsStableUnderCobaseChange := inverseImage_cobaseChange F W
  let : (W.inverseImage F).IsStableUnderCoproducts.{w} :=
    ⟨fun J => inverseImage_colimitsOfShape F W (Discrete J)⟩
  rw [I.llp_rlp_of_hasSmallObjectArgument']
  refine (MorphismProperty.retracts_le_iff (Q := W.inverseImage F)).mpr ?_
  let J := I.smallObjectκ.ord.ToType
  let : PreservesWellOrderContinuousOfShape J F := ⟨fun _ _ => inferInstance⟩
  intro X Y f hf
  have hc : (MorphismProperty.coproducts.{w} I).pushouts ≤ W.inverseImage F :=
    MorphismProperty.pushouts_le_iff.mpr (MorphismProperty.coproducts_le_iff.mpr hI)
  exact MorphismProperty.transfiniteCompositionsOfShape_le W J _
    (MorphismProperty.transfiniteCompositionsOfShape_map_of_preserves J F f
      (MorphismProperty.transfiniteCompositionsOfShape_monotone J hc _ hf))

end SerrePositivity.ModelGeneration
