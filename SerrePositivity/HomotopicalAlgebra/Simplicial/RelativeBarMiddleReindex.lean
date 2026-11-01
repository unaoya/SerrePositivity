module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarReindex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

/-!
# 相対barの中間対象の添字変更が局所化後に同型を与える

## 概要
相対barの中間対象の添字変更が局所化後に同型を与える。
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
[棚卸し m0526][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0526
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reindexing the actual middle of a relative bar span

The middle comparison commutes with both legs. Its image is invertible under
every anodyne-inverting functor, independently of cofinality of the index map.
-/

@[expose] public section
universe v uI vI uB vB uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {E D : Type uI} [Category.{vI} E] [Category.{vI} D]
  {B : Type uB} [Category.{vB} B] (q : E ⥤ D) (p : D ⥤ B) (F : D ⥤ SSet.{v})

abbrev middleReindexComma (e : E) (n : SimplexCategoryᵒᵖ) :
    CostructuredArrow (elementProjection (𝟭 E) (q ⋙ F) n) e ⥤
      CostructuredArrow (elementProjection (𝟭 D) F n) (q.obj e) :=
  CostructuredArrow.post (Functor.Elements.π ((q ⋙ F).flip.obj n)) q e ⋙
    CostructuredArrow.pre (Functor.Elements.precomp q (F.flip.obj n))
      (elementProjection (𝟭 D) F n) (q.obj e)

def middleReindexComponent (e : E) :
    (spanMiddle (q ⋙ p) (q ⋙ F)).obj e ⟶ (spanMiddle p F).obj (q.obj e) where
  app n := ↾fun x => ULift.up (x.down ⋙ middleReindexComma q F e n)
  naturality {_ _} _ := rfl

def middleReindex : spanMiddle (q ⋙ p) (q ⋙ F) ⟶ q ⋙ spanMiddle p F where
  app := middleReindexComponent q p F
  naturality {e e'} f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply congrArg ULift.up
    change (x.down ⋙ CostructuredArrow.map f) ⋙ middleReindexComma q F e' n =
      (x.down ⋙ middleReindexComma q F e n) ⋙ CostructuredArrow.map (q.map f)
    refine CategoryTheory.Functor.ext (fun i => congrArg
      (CostructuredArrow.mk (S := elementProjection (𝟭 D) F n)
        (Y := (Functor.Elements.precomp q (F.flip.obj n)).obj (x.down.obj i).left))
      (q.map_comp (x.down.obj i).hom f)) ?_
    intro i j h
    apply CostructuredArrow.hom_ext
    apply Functor.Elements.hom_ext
    simp

lemma middleReindex_left :
    middleReindex q p F ≫ Functor.whiskerLeft q (spanLeft p F) =
      spanLeft (q ⋙ p) (q ⋙ F) := by
  rfl

lemma middleReindex_right :
    middleReindex q p F ≫ Functor.whiskerLeft q (spanRight p F) =
      spanRight (q ⋙ p) (q ⋙ F) ≫
        Functor.whiskerLeft (q ⋙ p) (reindex q p F) := by
  rfl

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max uI vI v vB} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma middleReindex_image_isIso (e : E) : IsIso (L.map ((middleReindex q p F).app e)) := by
  have : IsIso (L.map ((spanLeft p F).app (q.obj e))) :=
    inferInstanceAs (IsIso (spanLeftImageIso p F L hL (q.obj e)).hom)
  have : IsIso (L.map ((spanLeft (q ⋙ p) (q ⋙ F)).app e)) :=
    inferInstanceAs (IsIso (spanLeftImageIso (q ⋙ p) (q ⋙ F) L hL e).hom)
  have h := congrArg (fun a => L.map (a.app e)) (middleReindex_left q p F)
  dsimp at h
  rw [L.map_comp] at h
  have : IsIso (L.map ((middleReindex q p F).app e) ≫
      L.map ((spanLeft p F).app (q.obj e))) := h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

/-- 相対barの中間対象の添字変更が局所化後に同型を与える。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数の要素の圏・comma圏とnerveを使って写像を構成する。
単体方向と基底方向の自然性を確認し、収縮や局所化の普遍性へ接続する。
-/
def middleReindexImageIso : spanMiddle (q ⋙ p) (q ⋙ F) ⋙ L ≅
    (q ⋙ spanMiddle p F) ⋙ L := by
  let a := Functor.whiskerRight (middleReindex q p F) L
  have : ∀ e, IsIso (a.app e) := middleReindex_image_isIso q p F L hL
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

include hL in
lemma reindexedRight_image_isIso_iff (e : E) :
    IsIso (L.map (((spanRight (q ⋙ p) (q ⋙ F)) ≫
      Functor.whiskerLeft (q ⋙ p) (reindex q p F)).app e)) ↔
        IsIso (L.map ((spanRight p F).app (q.obj e))) := by
  have := middleReindex_image_isIso q p F L hL e
  rw [← middleReindex_right, NatTrans.comp_app, Functor.whiskerLeft_app, L.map_comp]
  exact isIso_comp_left_iff _ _

end SerrePositivity.SimplicialModel.BarConstruction
