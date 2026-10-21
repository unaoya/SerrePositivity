module
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # 実 dg tensor の単位関手の monoidal 計算
概要：一対象の単位複体を持つ dg 圏との tensor の左右単位写像を照合する。
方針：元の単位自然性と tensorμ に関する左右単位の monoidal 法則を使う。
規約：具体的複体を展開しない。使われ方：Λ の oplax 単位則。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- 元の左単位写像は、元の閉単位の tensor を同じ閉単位へ送る。 -/
lemma dgTensorUnitor_left_unit {X : V} (a : 𝟙_ V ⟶ X) :
    ((λ_ (𝟙_ V)).inv ≫ (𝟙 (𝟙_ V) ⊗ₘ a)) ≫ (λ_ X).hom = a := by
  rw [id_tensorHom, Category.assoc, leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- 元の右単位写像は、元の閉単位の tensor を同じ閉単位へ送る。 -/
lemma dgTensorUnitor_right_unit {X : V} (a : 𝟙_ V ⟶ X) :
    ((λ_ (𝟙_ V)).inv ≫ (a ⊗ₘ 𝟙 (𝟙_ V))) ≫ (ρ_ X).hom = a := by
  rw [tensorHom_id, Category.assoc, rightUnitor_naturality, ← unitors_equal,
    Iso.inv_hom_id_assoc]

variable [BraidedCategory V]

/-- 元の左単位写像は、元の signed tensor の合成を保持する。 -/
lemma dgTensorUnitor_left_composition {X Y Z : V} (m : X ⊗ Y ⟶ Z) :
    (tensorμ (𝟙_ V) X (𝟙_ V) Y ≫ ((λ_ (𝟙_ V)).hom ⊗ₘ m)) ≫ (λ_ Z).hom =
      ((λ_ X).hom ⊗ₘ (λ_ Y).hom) ≫ m := by
  rw [← Category.comp_id (λ_ (𝟙_ V)).hom, ← Category.id_comp m,
    ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

/-- 元の右単位写像は、元の signed tensor の合成を保持する。 -/
lemma dgTensorUnitor_right_composition {X Y Z : V} (m : X ⊗ Y ⟶ Z) :
    (tensorμ X (𝟙_ V) Y (𝟙_ V) ≫ (m ⊗ₘ (λ_ (𝟙_ V)).hom)) ≫ (ρ_ Z).hom =
      ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom) ≫ m := by
  rw [← Category.id_comp m, ← Category.comp_id (λ_ (𝟙_ V)).hom,
    ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

end SerrePositivity.KST.SConstruction
