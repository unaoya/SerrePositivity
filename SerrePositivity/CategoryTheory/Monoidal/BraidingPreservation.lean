module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # モノイダル関手のbraidingの保存をテンソル積へ拡張する

二つの対象と固定された第三の対象とのbraidingを保存する場合、
その二対象のテンソル積と第三の対象とのbraidingも保存する。
hexagonとモノイダル関手の整合性を使う、スペクトルに依存しない一般論。
-/

@[expose] public section

universe v u v' u'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalFunctor

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
  CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]

/-- 二つの対象とのbraidingの保存から、そのテンソル積とのbraidingの保存を得る。 -/
lemma map_braiding_tensor_left (F : C ⥤ D) [F.Monoidal] (X Y Z : C)
    (hx : F.map (β_ X Z).hom = δ F X Z ≫ (β_ (F.obj X) (F.obj Z)).hom ≫ μ F Z X)
    (hy : F.map (β_ Y Z).hom = δ F Y Z ≫ (β_ (F.obj Y) (F.obj Z)).hom ≫ μ F Z Y) :
    F.map (β_ (X ⊗ Y) Z).hom =
      δ F (X ⊗ Y) Z ≫ (β_ (F.obj (X ⊗ Y)) (F.obj Z)).hom ≫ μ F Z (X ⊗ Y) := by
  rw [braiding_tensor_left_hom]
  simp only [CategoryTheory.Functor.map_comp, map_associator, map_associator_inv,
    map_whiskerLeft, map_whiskerRight, hx, hy, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  simp only [μ_δ_assoc, whiskerLeft_μ_δ_assoc, whiskerRight_μ_δ_assoc]
  rw [← braiding_tensor_left_hom_assoc, braiding_naturality_left_assoc]
  simp

end SerrePositivity.MonoidalFunctor
