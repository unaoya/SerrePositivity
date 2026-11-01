module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PushoutCotensor

/-!
# 内部Homは元のpushoutを実際のpullbackへ移す

## 概要
内部Homは元のpushoutを実際のpullbackへ移す。
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
[棚卸し m0517][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0517
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The original pushout gives an actual pullback of internal Hom objects
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.PushoutInternalHomPullback
variable {A B C P : SSet.{v}} {i : A ⟶ B} {j : A ⟶ C} {u : B ⟶ P} {g : C ⟶ P}

/-- 内部Homは元のpushoutを実際のpullbackへ移す。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma isPullback (sq : IsPushout i j u g) (K : SSet.{v}) :
    IsPullback ((pre u).app K) ((pre g).app K) ((pre i).app K) ((pre j).app K) := by
  have hw : (pre u).app K ≫ (pre i).app K = (pre g).app K ≫ (pre j).app K := by
    rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map, sq.w]
  apply IsPullback.of_isLimit' ⟨hw⟩
  refine PullbackCone.IsLimit.mk _
    (fun c => PushoutCotensor.glue sq c.fst c.snd c.condition)
    (fun c => PushoutCotensor.glue_left _ _ _ _) (fun c => PushoutCotensor.glue_right _ _ _ _)
    (fun c m hm hn => ?_)
  exact PushoutCotensor.hom_ext sq
    (hm.trans (PushoutCotensor.glue_left _ _ _ _).symm)
    (hn.trans (PushoutCotensor.glue_right _ _ _ _).symm)

end SerrePositivity.SimplicialModel.PushoutInternalHomPullback
