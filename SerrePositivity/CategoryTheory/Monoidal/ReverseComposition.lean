module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # 交換で因子の順序を逆にした合成の法則 -/

@[expose] public section

universe v u u'

namespace SerrePositivity.ReverseComposition

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [BraidedCategory V]

/-- 合成の入力の二つの因子の順序を交換する。 -/
def reverse {X Y Z : V} (m : Y ⊗ X ⟶ Z) : X ⊗ Y ⟶ Z := (β_ X Y).hom ≫ m

/-- 三つの因子を逆順へ移す二つの経路は一致する。 -/
lemma reverse_three (X Y Z : V) :
    (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (β_ (Y ⊗ X) Z).hom =
    X ◁ (β_ Y Z).hom ≫ (β_ X (Z ⊗ Y)).hom ≫ (α_ Z Y X).hom := by
  rw [braiding_tensor_left_hom, braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact yang_baxter X Y Z

/-- 後から適用する射を左因子に置く結合則を、逆順の合成の結合則へ移す。 -/
lemma associativity {A B C D E F : V} (m₁ : B ⊗ A ⟶ D) (m₂ : C ⊗ B ⟶ E)
    (m₃ : C ⊗ D ⟶ F) (m₄ : E ⊗ A ⟶ F)
    (h : m₂ ▷ A ≫ m₄ = (α_ C B A).hom ≫ C ◁ m₁ ≫ m₃) :
    (α_ A B C).inv ≫ reverse m₁ ▷ C ≫ reverse m₃ =
      A ◁ reverse m₂ ≫ reverse m₄ := by
  unfold reverse
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [braiding_naturality_left_assoc, braiding_naturality_right_assoc, h]
  rw [← reassoc_of% (reverse_three A B C)]

/-- 逆順の合成の左単位則は、元の合成の右単位則から得られる。 -/
lemma left_unit {X U : V} (e : 𝟙_ V ⟶ U) (m : X ⊗ U ⟶ X)
    (h : X ◁ e ≫ m = (ρ_ X).hom) :
    (λ_ X).inv ≫ e ▷ X ≫ reverse m = 𝟙 X := by
  unfold reverse
  rw [braiding_naturality_left_assoc, h, braiding_rightUnitor, Iso.inv_hom_id]

/-- 逆順の合成の右単位則は、元の合成の左単位則から得られる。 -/
lemma right_unit {X U : V} (e : 𝟙_ V ⟶ U) (m : U ⊗ X ⟶ X)
    (h : e ▷ X ≫ m = (λ_ X).hom) :
    (ρ_ X).inv ≫ X ◁ e ≫ reverse m = 𝟙 X := by
  unfold reverse
  rw [braiding_naturality_right_assoc, h, braiding_leftUnitor, Iso.inv_hom_id]

/-- 後から適用する射を左に置く合成から、通常の因子順の豊穣圏を構成する。 -/
@[instance_reducible]
def enrichedCategory (C : Type u') (Hom : C → C → V)
    (e : ∀ X, 𝟙_ V ⟶ Hom X X)
    (m : ∀ X Y Z, Hom Y Z ⊗ Hom X Y ⟶ Hom X Z)
    (hl : ∀ X Y, (e Y ⊗ₘ 𝟙 (Hom X Y)) ≫ m X Y Y = (λ_ (Hom X Y)).hom)
    (hr : ∀ X Y, (𝟙 (Hom X Y) ⊗ₘ e X) ≫ m X X Y = (ρ_ (Hom X Y)).hom)
    (ha : ∀ W X Y Z, (m X Y Z ⊗ₘ 𝟙 (Hom W X)) ≫ m W X Z =
      (α_ (Hom Y Z) (Hom X Y) (Hom W X)).hom ≫
        (𝟙 (Hom Y Z) ⊗ₘ m W X Y) ≫ m W Y Z) : EnrichedCategory V C where
  Hom := Hom
  id := e
  comp X Y Z := reverse (m X Y Z)
  id_comp X Y := by
    apply left_unit (e X) (m X X Y)
    have h := hr X Y
    rw [id_tensorHom] at h
    exact h
  comp_id X Y := by
    apply right_unit (e Y) (m X Y Y)
    have h := hl X Y
    rw [tensorHom_id] at h
    exact h
  assoc W X Y Z := by
    apply associativity (m W X Y) (m X Y Z) (m W Y Z) (m W X Z)
    have h := ha W X Y Z
    rw [tensorHom_id, id_tensorHom] at h
    exact h

end SerrePositivity.ReverseComposition
