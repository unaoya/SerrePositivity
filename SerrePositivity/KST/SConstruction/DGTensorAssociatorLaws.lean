module
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # tensor dg 結合関手に使う抽象 monoidal の式
概要：単位三つの結合と、六つの Hom の tensorμ の結合を抽象基底で照合する。
方針：単位の coherence と tensorμ の monoidal 結合則を使う。
規約：具体的な複体や dg 圏を展開しない。使われ方：元の tensor dg 結合関手。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category V] [MonoidalCategory V]

/-- 三つの元の閉単位の tensor は、元の結合写像で二つの括弧を比較できる。 -/
lemma dgTensorAssociator_unit {X Y Z : V}
    (a : 𝟙_ V ⟶ X) (b : 𝟙_ V ⟶ Y) (c : 𝟙_ V ⟶ Z) :
    (λ_ (𝟙_ V)).inv ≫ (((λ_ (𝟙_ V)).inv ≫ (a ⊗ₘ b)) ⊗ₘ c) ≫ (α_ X Y Z).hom =
      (λ_ (𝟙_ V)).inv ≫ (a ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (b ⊗ₘ c))) := by
  have hl : (((λ_ (𝟙_ V)).inv ≫ (a ⊗ₘ b)) ⊗ₘ c) =
      ((λ_ (𝟙_ V)).inv ⊗ₘ 𝟙 (𝟙_ V)) ≫ ((a ⊗ₘ b) ⊗ₘ c) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hr : (a ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (b ⊗ₘ c))) =
      (𝟙 (𝟙_ V) ⊗ₘ (λ_ (𝟙_ V)).inv) ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hl, hr]
  simp only [Category.assoc]
  rw [associator_naturality]
  simp only [← Category.assoc]
  congr 1
  monoidal

variable [BraidedCategory V]

/-- 元の三つの合成写像と tensorμ は、同じ monoidal 結合写像と交換する。 -/
lemma dgTensorAssociator_composition {A B C D E F X Y Z : V}
    (f : A ⊗ D ⟶ X) (g : B ⊗ E ⟶ Y) (h : C ⊗ F ⟶ Z) :
    tensorμ (A ⊗ B) C (D ⊗ E) F ≫
        ((tensorμ A B D E ≫ (f ⊗ₘ g)) ⊗ₘ h) ≫ (α_ X Y Z).hom =
      ((α_ A B C).hom ⊗ₘ (α_ D E F).hom) ≫ tensorμ A (B ⊗ C) D (E ⊗ F) ≫
        (f ⊗ₘ (tensorμ B C E F ≫ (g ⊗ₘ h))) := by
  rw [tensorHom_def, comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [← tensorHom_def_assoc, associator_naturality, associator_monoidal_assoc]
  simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]

end SerrePositivity.KST.SConstruction
