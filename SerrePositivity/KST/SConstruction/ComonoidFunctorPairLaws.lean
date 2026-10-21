module
public import SerrePositivity.KST.SConstruction.ComonoidTensorDiagonal

/-! # 余モノイド対角からの任意出力の結合・単位則
概要：同じ余モノイドからの任意の三つの射を、対角で束ねたときの法則を示す。
方針：元の余モノイドの結合・増大則と tensor・結合・単位の自然性を使う。
規約：出力の余モノイド構造は要求しない。使われ方：実 dg 関手の組の全 Hom。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open scoped ComonObj
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 元の対角で三つの任意出力を束ねる二つの順序は、元の結合射で一致する。 -/
lemma comonoidFunctorPair_associativity (P : Comon C) {X Y Z : C}
    (f : P.X ⟶ X) (g : P.X ⟶ Y) (h : P.X ⟶ Z) :
    (Δ[P.X] ≫ ((Δ[P.X] ≫ (f ⊗ₘ g)) ⊗ₘ h)) ≫ (α_ X Y Z).hom =
      Δ[P.X] ≫ (f ⊗ₘ (Δ[P.X] ≫ (g ⊗ₘ h))) := by
  have hl : ((Δ[P.X] ≫ (f ⊗ₘ g)) ⊗ₘ h) =
      (Δ[P.X] ⊗ₘ 𝟙 P.X) ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hr : (f ⊗ₘ (Δ[P.X] ≫ (g ⊗ₘ h))) =
      (𝟙 P.X ⊗ₘ Δ[P.X]) ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hl, hr]
  simp only [Category.assoc]
  rw [associator_naturality]
  simp only [← Category.assoc]
  rw [comonoidDiagonal_associativity]

/-- 元の対角の左因子を増大すると、元の任意の右出力を回収する。 -/
lemma comonoidFunctorPair_left_unit (P : Comon C) {X : C} (f : P.X ⟶ X) :
    (Δ[P.X] ≫ (ε[P.X] ⊗ₘ f)) ≫ (λ_ X).hom = f := by
  have h : (ε[P.X] ⊗ₘ f) =
      (ε[P.X] ⊗ₘ 𝟙 P.X) ≫ (𝟙 (𝟙_ C) ⊗ₘ f) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc]
  rw [id_tensorHom, leftUnitor_naturality]
  rw [← Category.assoc, ← Category.assoc, comonoidDiagonal_left_counit, Category.id_comp]

/-- 元の対角の右因子を増大すると、元の任意の左出力を回収する。 -/
lemma comonoidFunctorPair_right_unit (P : Comon C) {X : C} (f : P.X ⟶ X) :
    (Δ[P.X] ≫ (f ⊗ₘ ε[P.X])) ≫ (ρ_ X).hom = f := by
  have h : (f ⊗ₘ ε[P.X]) =
      (𝟙 P.X ⊗ₘ ε[P.X]) ≫ (f ⊗ₘ 𝟙 (𝟙_ C)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [h]
  simp only [Category.assoc]
  rw [tensorHom_id, rightUnitor_naturality]
  rw [← Category.assoc, ← Category.assoc, comonoidDiagonal_right_counit, Category.id_comp]

end SerrePositivity.KST.SConstruction
