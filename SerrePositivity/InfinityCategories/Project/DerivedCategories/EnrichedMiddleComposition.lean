module
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
/-!
概要：実閉射を中央に挟む二通りの全 Hom 豊穣合成が厳密に一致する。
方針：豊穣結合律と単位子の三角式を使い、閉射の前後合成を比較する。
規約：任意の豊穣通常圏。使われ方：出力分解 dg 合成の比較差の中間項の消去。
-/
@[expose] public section
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
/-- 中央の実閉射は、左 Hom への後合成と右 Hom への前合成の間で移せる。 -/
lemma enrichedComposition_middle (V : Type u) [Category.{v} V] [MonoidalCategory V]
    (C : Type w) [Category.{z} C] [EnrichedOrdinaryCategory V C]
    (X Y Y' Z : C) (f : Y ⟶ Y') :
    eHomWhiskerLeft V X f ▷ (Y' ⟶[V] Z) ≫ eComp V X Y' Z =
      (X ⟶[V] Y) ◁ eHomWhiskerRight V f Z ≫ eComp V X Y Z := by
  dsimp only [eHomWhiskerLeft, eHomWhiskerRight]
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  rw [← e_assoc', associator_naturality_middle_assoc, triangle_assoc_comp_right_inv_assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
