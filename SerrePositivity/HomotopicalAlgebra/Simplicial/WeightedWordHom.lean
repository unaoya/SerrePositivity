module

public import SerrePositivity.CategoryTheory.Quiver.WeightedPathMaps
public import SerrePositivity.HomotopicalAlgebra.Simplicial.WordPresentationDiagram
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 中断した任意モデル源への一般化：WeightedWordHom

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：An explicit contraction of word-weighted paths onto their underlying paths。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0606][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0606
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# An explicit contraction of word-weighted paths onto their underlying paths
-/

@[expose] public section
universe u v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.QuiverWeightedPaths

namespace SerrePositivity.SimplicialModel.WeightedWordHom
variable (V : Type u) [Quiver.{v} V] (X Y : V)

def hom : SSet.{max u v} where
  obj n := Path V (WordSegment.degree.{max u v} n) X Y
  map θ := ↾(mapWeights (WordSegment.degreeMap θ))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro p
    change mapWeights (WordSegment.degreeMap (𝟙 n)) p = p
    rw [WordPresentationDiagram.degreeMap_id]
    exact mapWeights_id p
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro p
    change mapWeights (WordSegment.degreeMap (θ ≫ φ)) p =
      mapWeights (WordSegment.degreeMap φ) (mapWeights (WordSegment.degreeMap θ) p)
    rw [mapWeights_comp, WordPresentationDiagram.degreeMap_comp]
    rfl

abbrev base : SSet.{max u v} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{max u v} (Quiver.Path X Y))

def projection : hom V X Y ⟶ base V X Y where
  app _ := ↾fun p => ULift.up (forget p)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg ULift.up (forget_mapWeights (WordSegment.degreeMap θ) p)

def section_ : base V X Y ⟶ hom V X Y where
  app _ := ↾fun p => fill 0 p.down
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro p
    change fill 0 p.down = mapWeights (WordSegment.degreeMap θ) (fill 0 p.down)
    rw [mapWeights_fill, map_zero]

lemma section_projection : section_ V X Y ≫ projection V X Y = 𝟙 _ := by
  ext n p
  exact congrArg ULift.up (forget_fill (0 : WordSegment.degree.{max u v} n) p.down)

def sandwich : hom V X Y ⊗ WordSegment.interval ⟶ hom V X Y where
  app _ := ↾fun x => mapWeights (fun a => a * WordSegment.letter.app _ x.2) x.1
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    change mapWeights (fun a => a * WordSegment.letter.app m (WordSegment.interval.map θ x.2))
      (mapWeights (WordSegment.degreeMap θ) x.1) =
        mapWeights (WordSegment.degreeMap θ)
          (mapWeights (fun a => a * WordSegment.letter.app n x.2) x.1)
    rw [mapWeights_comp, mapWeights_comp]
    congr 1
    funext a
    change WordSegment.degreeMap θ a *
      WordSegment.letter.app m (WordSegment.interval.map θ x.2) =
        WordSegment.degreeMap θ (a * WordSegment.letter.app n x.2)
    rw [map_mul]
    exact congrArg (fun t => WordSegment.degreeMap θ a * t)
      (types_congr_hom (WordSegment.letter.naturality θ) x.2)

def contraction : SSet.Homotopy (𝟙 (hom V X Y)) (projection V X Y ≫ section_ V X Y) where
  h := sandwich V X Y
  h₀ := by
    ext n p
    change mapWeights (fun a => a * WordSegment.letter.app n (WordSegment.endpoint n 0)) p = p
    rw [WordSegment.letter_unit]
    have h : (fun a : WordSegment.degree.{max u v} n => a * 1) = id := funext mul_one
    rw [h, mapWeights_id]
  h₁ := by
    ext n p
    change mapWeights (fun a => a * WordSegment.letter.app n (WordSegment.endpoint n 1)) p =
      fill 0 (forget p)
    rw [WordSegment.letter_zero]
    have h : (fun a : WordSegment.degree.{max u v} n => a * 0) = fun _ => 0 := funext mul_zero
    rw [h, mapWeights_const]
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
def comparisonIso : L.obj (hom V X Y) ≅ L.obj (base V X Y) :=
  AnodyneHomotopy.mapRetractionIso L hL (projection V X Y) (section_ V X Y)
    (section_projection V X Y) (contraction V X Y)

lemma localized_projection_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (projection V X Y)) :=
  (comparisonIso V X Y AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.SimplicialModel.WeightedWordHom
