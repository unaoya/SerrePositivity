module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedParameterizedUnit
/-!
概要：任意の三つの実パラメータ射について、豊穣三重合成の括弧変更を比較する。
方針：tensor と結合子の自然性を、実豊穣結合律へ前合成する。
使われ方：出力分解の結合律の実二射影。
-/
@[expose] public section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
/-- 三つの実パラメータからの豊穣合成は、同じ結合子と可換。 -/
lemma parameterEnriched_associativity (V : Type u) [Category.{v} V] [MonoidalCategory V]
    (C : Type w) [EnrichedCategory V C] (W X Y Z : C) {P Q T : V}
    (a : P ⟶ (W ⟶[V] X)) (b : Q ⟶ (X ⟶[V] Y)) (c : T ⟶ (Y ⟶[V] Z)) :
    (((a ⊗ₘ b) ≫ eComp V W X Y) ⊗ₘ c) ≫ eComp V W Y Z =
      (α_ P Q T).hom ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ eComp V X Y Z)) ≫ eComp V W X Z := by
  have hl : (((a ⊗ₘ b) ≫ eComp V W X Y) ⊗ₘ c) =
      ((a ⊗ₘ b) ⊗ₘ c) ≫ eComp V W X Y ▷ (Y ⟶[V] Z) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have hr : (a ⊗ₘ ((b ⊗ₘ c) ≫ eComp V X Y Z)) =
      (a ⊗ₘ (b ⊗ₘ c)) ≫ (W ⟶[V] X) ◁ eComp V X Y Z := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [hl, hr, Category.assoc, ← e_assoc', ← Category.assoc,
    associator_naturality, Category.assoc]
  simp only [Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
