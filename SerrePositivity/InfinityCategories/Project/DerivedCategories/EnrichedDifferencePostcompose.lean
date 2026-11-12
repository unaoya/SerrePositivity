module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedMiddleComposition
public import Mathlib.CategoryTheory.Preadditive.Basic
/-!
概要：全 Hom 自然な四角形に沿う後合成は、比較差の二項を同時に保つ。
方針：豊穣前後合成の交換則・合成則と差の線形性を使う。
規約：任意の豊穣通常圏で全パラメータを保持する。使われ方：出力分解 Hom の比較。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
/-- 同じ自然な四角形に沿う後合成は、元の比較差を新しい比較差へ送る。 -/
lemma enrichedDifference_postcompose (V : Type u) [Category.{v} V] [MonoidalCategory V]
    [Preadditive V] (C : Type w) [Category.{z} C] [EnrichedOrdinaryCategory V C]
    (K : V) (P Q X Y X' Y' : C)
    (f : K ⟶ (X ⟶[V] Y)) (g : K ⟶ (X' ⟶[V] Y')) (b : K ⟶ (P ⟶[V] Q))
    (p : P ⟶ X) (q : Q ⟶ Y) (a : X ⟶ X') (c : Y ⟶ Y')
    (h : f ≫ eHomWhiskerLeft V X c = g ≫ eHomWhiskerRight V a Y') :
    (f ≫ eHomWhiskerRight V p Y - b ≫ eHomWhiskerLeft V P q) ≫
        eHomWhiskerLeft V P c =
      g ≫ eHomWhiskerRight V (p ≫ a) Y' - b ≫ eHomWhiskerLeft V P (q ≫ c) := by
  rw [Preadditive.sub_comp]
  congr 1
  · rw [Category.assoc, ← eHom_whisker_exchange, ← Category.assoc, h]
    simp only [Category.assoc, eHomWhiskerRight_comp]
  · simp only [Category.assoc, eHomWhiskerLeft_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
