module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

/-!
# bar比較spanの右脚の可逆性をその源section上の可逆性へ帰着する

## 概要
bar比較spanの右脚の可逆性をその源section上の可逆性へ帰着する。
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
[棚卸し m0529][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0529
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual right bar leg is detected on its source section

The source section becomes invertible using the already proved left-leg
contraction. Thus testing the right leg reduces to an actual comma section.
-/

@[expose] public section
universe v uD vD uB vB vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})

lemma spanSection_right (d : D) : spanSection p F d ≫ (spanRight p F).app d =
    commaSection p F (𝟙 (p.obj d)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  let A := (Functor.const (Fin (n.unop.len + 1))).obj (identityPoint F d n x.down) ⋙
    CostructuredArrow.post (Functor.Elements.π (F.flip.obj n)) p d
  let B := (Functor.const (Fin (n.unop.len + 1))).obj
    (sectionPoint p F (𝟙 (p.obj d)) n x.down)
  change A = B
  have hobj (i : Fin (n.unop.len + 1)) : A.obj i = B.obj i :=
    congrArg (fun k => sectionPoint p F k n x.down) (p.map_id d)
  apply CategoryTheory.Functor.hext hobj
  intro i j f
  apply elementComma_hom_heq p F (hobj i) (hobj j)
  rfl

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max uD vD v vB} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma spanSection_image_isIso (d : D) : IsIso (L.map (spanSection p F d)) := by
  have : IsIso (L.map ((spanLeft p F).app d)) :=
    inferInstanceAs (IsIso (spanLeftImageIso p F L hL d).hom)
  apply (isIso_comp_right_iff (L.map (spanSection p F d))
    (L.map ((spanLeft p F).app d))).mp
  rw [← L.map_comp, spanSection_retract, L.map_id]
  infer_instance

include hL in
/-- bar比較spanの右脚の可逆性をその源section上の可逆性へ帰着する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
lemma spanRight_isIso_iff_section (d : D) : IsIso (L.map ((spanRight p F).app d)) ↔
    IsIso (L.map (commaSection p F (𝟙 (p.obj d)))) := by
  have := spanSection_image_isIso p F L hL d
  rw [← spanSection_right, L.map_comp]
  exact (isIso_comp_left_iff _ _).symm

end SerrePositivity.SimplicialModel.BarConstruction
