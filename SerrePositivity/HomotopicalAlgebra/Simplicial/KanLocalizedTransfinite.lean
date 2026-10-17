module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
# 局所化で可逆な単射の連続な超限合成も局所化で可逆となる

## 概要
局所化で可逆な単射の連続な超限合成も局所化で可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0421][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0421
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Transfinite closure of localized mono equivalences in any value universe

The fixed lifting-class characterization handles limit stages, including
those of small cofinality. No value model structure or colimit preservation
by the localization functor is assumed.
-/

@[expose] public section
universe w v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanLocalizedTransfinite
open KanTestLiftingClass

lemma stableOfShape (J : Type v) [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] : localizedMonos.{v}.IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    rintro A B f ⟨d⟩
    have hm : (MorphismProperty.monomorphisms SSet.{v}).transfiniteCompositionsOfShape J f :=
      ⟨d.ofLE (fun _ _ _ h => h.1)⟩
    have hl : rightTests.llp.transfiniteCompositionsOfShape J f :=
      ⟨d.ofLE localizedMono_le_llp⟩
    exact ⟨(MorphismProperty.monomorphisms SSet.{v}).transfiniteCompositionsOfShape_le J f hm,
      localized_isIso_of_llp f (rightTests.llp.transfiniteCompositionsOfShape_le J f hl)⟩

instance stableSmallOfShape (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] :
    localizedMonos.{v}.IsStableUnderTransfiniteCompositionOfShape J :=
  (MorphismProperty.isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso
    localizedMonos (orderIsoShrink.{v} J)).mpr (stableOfShape _)

instance stable : MorphismProperty.IsStableUnderTransfiniteComposition.{v} localizedMonos.{v} where

lemma localized_isIso (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] {A B : SSet.{v}} (f : A ⟶ B)
    (d : localizedMonos.TransfiniteCompositionOfShape J f) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) :=
  (localizedMonos.transfiniteCompositionsOfShape_le J f ⟨d⟩).2

lemma image_isIso (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] {A B : SSet.{v}} (f : A ⟶ B)
    (d : localizedMonos.TransfiniteCompositionOfShape J f)
    {D : Type uH} [Category.{vH} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map f) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL f (localized_isIso J f d)

/-- 局所化で可逆な単射の連続な超限合成も局所化で可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma cocone_mem (J : Type w) [Small.{v} J] [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] (F : J ⥤ SSet.{v}) [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬IsMax j → localizedMonos (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : localizedMonos (c.ι.app ⊥) := by
  let d : localizedMonos.TransfiniteCompositionOfShape J (c.ι.app ⊥) :=
    { F := F, isoBot := Iso.refl _, incl := c.ι, isColimit := hc, map_mem := hF }
  exact localizedMonos.transfiniteCompositionsOfShape_le J _ ⟨d⟩

lemma sequential_cocone_mem (F : ℕ ⥤ SSet.{v})
    (hF : ∀ n, localizedMonos (F.map (homOfLE (Nat.le_succ n))))
    (c : Cocone F) (hc : IsColimit c) : localizedMonos (c.ι.app 0) :=
  cocone_mem ℕ F (fun n _ => hF n) c hc

end SerrePositivity.SimplicialModel.KanLocalizedTransfinite
