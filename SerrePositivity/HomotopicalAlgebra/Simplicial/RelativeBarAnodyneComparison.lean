module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 相対bar比較spanの左脚がanodyne局所化後に実際の自然同型となる

## 概要
相対bar比較spanの左脚がanodyne局所化後に実際の自然同型となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0519][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0519
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The entire left bar comparison becomes a natural isomorphism after anodyne inversion

This applies in the enlarged auxiliary universe without a model structure.
The comparison retains the actual natural left leg as its components.
-/

@[expose] public section
universe v uD vD uB vB vH uH
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})
  {H : Type uH} [Category.{vH} H] (L : SSet.{max uD vD v vB} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

/-- Pointwise inverse maps are the images of the already chosen actual sections. -/
def spanLeftImageIso (d : D) : L.obj ((spanMiddle p F).obj d) ≅
    L.obj ((F ⋙ SSet.uliftFunctor.{max uD vD vB, v}).obj d) :=
  AnodyneHomotopy.mapRetractionIso L hL ((spanLeft p F).app d) (spanSection p F d)
    (spanSection_retract p F d) (spanLeftHomotopy p F d)

/-- Naturality comes from the actual left leg; the pointwise inverses need no separate choice. -/
def spanLeftComparisonIso : spanMiddle p F ⋙ L ≅
    (F ⋙ SSet.uliftFunctor.{max uD vD vB, v}) ⋙ L := by
  let a := Functor.whiskerRight (spanLeft p F) L
  have : ∀ d, IsIso (a.app d) := fun d =>
    inferInstanceAs (IsIso (spanLeftImageIso p F L hL d).hom)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

lemma spanLeftComparisonIso_hom_app (d : D) :
    (spanLeftComparisonIso p F L hL).hom.app d = L.map ((spanLeft p F).app d) := rfl

/-- 相対bar比較spanの左脚がanodyne局所化後に実際の自然同型となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
abbrev spanLeftAnodyneIso : spanMiddle p F ⋙ AnodyneHomotopy.anodyneQ ≅
    (F ⋙ SSet.uliftFunctor.{max uD vD vB, v}) ⋙ AnodyneHomotopy.anodyneQ :=
  spanLeftComparisonIso p F AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)

end SerrePositivity.SimplicialModel.BarConstruction
