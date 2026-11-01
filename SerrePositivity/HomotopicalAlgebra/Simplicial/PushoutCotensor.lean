module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-!
# 実際のpushoutの二つの脚に沿って互換な余テンソル族を貼り合わせる

## 概要
実際のpushoutの二つの脚に沿って互換な余テンソル族を貼り合わせる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0516][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0516
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing whole cotensor families on an actual pushout square
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel.BoundaryCotensor

namespace SerrePositivity.SimplicialModel.PushoutCotensor
variable {A B C Q T P : SSet.{w}} {u : A ⟶ B} {v : A ⟶ C} {l : B ⟶ Q} {r : C ⟶ Q}
  (sq : IsPushout u v l r) (b : T ⟶ (ihom B).obj P) (c : T ⟶ (ihom C).obj P)
  (h : b ≫ (pre u).app P = c ≫ (pre v).app P)

include h in
lemma transpose_compatible : u ≫ transpose b = v ≫ transpose c := by
  rw [← transpose_restriction, ← transpose_restriction, h]

/-- 実際のpushoutの二つの脚に沿って互換な余テンソル族を貼り合わせる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def glue : T ⟶ (ihom Q).obj P := transpose (sq.desc (transpose b) (transpose c)
  (transpose_compatible b c h))

@[reassoc]
lemma glue_left : glue sq b c h ≫ (pre l).app P = b := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose, sq.inl_desc]

@[reassoc]
lemma glue_right : glue sq b c h ≫ (pre r).app P = c := by
  apply transpose_injective
  rw [transpose_restriction, glue, transpose_transpose, sq.inr_desc]

include sq in
lemma hom_ext {f g : T ⟶ (ihom Q).obj P}
    (hl : f ≫ (pre l).app P = g ≫ (pre l).app P)
    (hr : f ≫ (pre r).app P = g ≫ (pre r).app P) : f = g := by
  apply transpose_injective
  apply sq.hom_ext
  · rw [← transpose_restriction, ← transpose_restriction, hl]
  · rw [← transpose_restriction, ← transpose_restriction, hr]

end SerrePositivity.SimplicialModel.PushoutCotensor
