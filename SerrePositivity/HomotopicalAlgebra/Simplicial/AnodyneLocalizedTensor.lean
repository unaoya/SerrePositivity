module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# anodyne局所化で可逆な射に左から直積を取っても局所化で可逆となる

## 概要
anodyne局所化で可逆な射に左から直積を取っても局所化で可逆となる。
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
[棚卸し m0343][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0343
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Cartesian tensor preserves every anodyne-localized equivalence

The tensor functors preserve the actual anodyne generators and their
closure. The localization universal property then handles every inverted
map, without a model structure in the value universe.
-/

@[expose] public section
universe v uH vH
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.AnodyneHomotopy
variable {X Y : SSet.{v}} (f : X ⟶ Y) (hf : IsIso (anodyneQ.map f)) (A : SSet.{v})
  {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hf hL in
lemma whiskerLeft_image_isIso : IsIso (L.map (A ◁ f)) := by
  let T := tensorLeft A ⋙ L
  have hT : SSet.anodyneExtensions.IsInvertedBy T := by
    intro U V g hg
    exact hL _ (hg.whiskerLeft A)
  exact map_isIso_of_anodyneQ_isIso T hT f hf

include hf hL in
lemma whiskerRight_image_isIso : IsIso (L.map (f ▷ A)) := by
  let T := tensorRight A ⋙ L
  have hT : SSet.anodyneExtensions.IsInvertedBy T := by
    intro U V g hg
    exact hL _ (hg.whiskerRight A)
  exact map_isIso_of_anodyneQ_isIso T hT f hf

include hf in
/-- anodyne局所化で可逆な射に左から直積を取っても局所化で可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma whiskerLeft_anodyneQ_isIso : IsIso (anodyneQ.map (A ◁ f)) :=
  whiskerLeft_image_isIso f hf A anodyneQ (Localization.inverts anodyneQ SSet.anodyneExtensions)

include hf in
lemma whiskerRight_anodyneQ_isIso : IsIso (anodyneQ.map (f ▷ A)) :=
  whiskerRight_image_isIso f hf A anodyneQ (Localization.inverts anodyneQ SSet.anodyneExtensions)

end SerrePositivity.SimplicialModel.AnodyneHomotopy
