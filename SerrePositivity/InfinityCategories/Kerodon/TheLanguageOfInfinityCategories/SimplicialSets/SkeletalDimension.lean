module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# 指定した次元範囲で骨格段階を元の単体的集合と同型で結ぶ

## 概要
指定した次元範囲で骨格段階を元の単体的集合と同型で結ぶ。
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
[棚卸し m0570][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0570
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17

対応節は Kerodon 1.1（Tag 0004）。
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual skeletal stage is the whole object in its dimension range
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
variable {A X : SSet.{v}} (i : A ⟶ X)

lemma eq_top (n : ℕ) [X.HasDimensionLT n] : SSet.skeletonOfMono i n = ⊤ := by
  rw [SSet.Subcomplex.eq_top_iff_of_hasDimensionLT _ n]
  intro d hd x _
  rw [SSet.skeletonOfMono_obj_eq_top i hd]
  trivial

/-- 指定した次元範囲で骨格段階を元の単体的集合と同型で結ぶ。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def stageIso (n : ℕ) [X.HasDimensionLT n] :
    (SSet.skeletonOfMono i n).toSSet ≅ X :=
  SSet.Subcomplex.eqToIso (eq_top i n) ≪≫ SSet.Subcomplex.topIso X

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
