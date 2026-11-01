module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 中断した任意モデル源への一般化：OrdinaryBarDiagonalHomRetraction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：An explicit all-degree Hom retraction without a large simplicial model structure。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0159][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0159
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# An explicit all-degree Hom retraction without a large simplicial model structure
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction
open OrdinaryBarFreeResolutionSeed OrdinaryBarFixedWordResolution OrdinaryBarDiagonalAmbientHom
variable (C : Type u) [Category.{v} C]

def sandwich (X Y : D C) : ambientHom C X Y ⊗ WordSegment.interval ⟶ ambientHom C X Y where
  app n := ↾fun x => wordAt C n X (WordSegment.letter.app n x.2) ≫ x.1 ≫
    wordAt C n Y (WordSegment.letter.app n x.2)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    change wordAt C m X (WordSegment.letter.app m (WordSegment.interval.map θ x.2)) ≫
      ((diagram C).map θ).toFunctor.map x.1 ≫
        wordAt C m Y (WordSegment.letter.app m (WordSegment.interval.map θ x.2)) =
          ((diagram C).map θ).toFunctor.map
            (wordAt C n X (WordSegment.letter.app n x.2) ≫ x.1 ≫
              wordAt C n Y (WordSegment.letter.app n x.2))
    rw [Functor.map_comp, Functor.map_comp, map_word, map_word]
    have h := types_congr_hom (WordSegment.letter.naturality θ) x.2
    change WordSegment.letter.app _ (WordSegment.interval.map θ x.2) =
      WordSegment.degreeMap θ (WordSegment.letter.app _ x.2) at h
    rw [h]

def contraction (X Y : D C) :
    SSet.Homotopy (𝟙 (ambientHom C X Y)) (transfer C X Y ≫ inclusion C X Y) where
  h := sandwich C X Y
  h₀ := by
    ext n f
    change wordAt C n X (WordSegment.letter.app n (WordSegment.endpoint n 0)) ≫ f ≫
      wordAt C n Y (WordSegment.letter.app n (WordSegment.endpoint n 0)) = f
    rw [WordSegment.letter_unit, wordAt, wordAt, RetractWords.quotient_word_one,
      RetractWords.quotient_word_one, Category.id_comp, Category.comp_id]
  h₁ := by
    ext n f
    change wordAt C n X (WordSegment.letter.app n (WordSegment.endpoint n 1)) ≫ f ≫
      wordAt C n Y (WordSegment.letter.app n (WordSegment.endpoint n 1)) =
        projectionAt C n X ≫ (sectionAt C n X ≫ f ≫ projectionAt C n Y) ≫ sectionAt C n Y
    rw [WordSegment.letter_zero, wordAt, wordAt, RetractWords.quotient_word_zero,
      RetractWords.quotient_word_zero]
    simp only [Category.assoc]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
def comparisonIso (X Y : D C) : L.obj (ambientHom C X Y) ≅ L.obj (hom C X Y) :=
  AnodyneHomotopy.mapRetractionIso L hL (transfer C X Y) (inclusion C X Y)
    (inclusion_transfer C X Y) (contraction C X Y)

lemma localized_transfer_isIso (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (transfer C X Y)) :=
  (comparisonIso C AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) X Y).isIso_hom

lemma localized_inclusion_isIso (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (inclusion C X Y)) :=
  (comparisonIso C AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) X Y).isIso_inv

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction
