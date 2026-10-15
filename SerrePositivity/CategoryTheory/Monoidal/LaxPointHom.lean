module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # lax monoidal関手による単位からの射の移送 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace SerrePositivity.LaxPointHom

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor.LaxMonoidal

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [MonoidalCategory V] [MonoidalCategory W] (F : V ⥤ W) [F.LaxMonoidal]

/-- 関手の単位比較を使って単位からの射を送る。 -/
def map {X : V} (f : 𝟙_ V ⟶ X) : 𝟙_ W ⟶ F.obj X := ε F ≫ F.map f

lemma left_action {X Y Z : V} (f : 𝟙_ V ⟶ X) (m : X ⊗ Y ⟶ Z) :
    (λ_ (F.obj Y)).inv ≫ map F f ▷ F.obj Y ≫ μ F X Y ≫ F.map m =
      F.map ((λ_ Y).inv ≫ f ▷ Y ≫ m) := by
  unfold map
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [μ_natural_left_assoc, left_unitality_inv_assoc]
  simp only [F.map_comp]

lemma right_action {X Y Z : V} (f : 𝟙_ V ⟶ Y) (m : X ⊗ Y ⟶ Z) :
    (ρ_ (F.obj X)).inv ≫ F.obj X ◁ map F f ≫ μ F X Y ≫ F.map m =
      F.map ((ρ_ X).inv ≫ X ◁ f ≫ m) := by
  unfold map
  rw [whiskerLeft_comp]
  simp only [Category.assoc]
  rw [μ_natural_right_assoc, right_unitality_inv_assoc]
  simp only [F.map_comp]

/-- 単位からの二つの射の合成はlax monoidalの比較と両立する。 -/
lemma composition {X Y Z : V} (f : 𝟙_ V ⟶ X) (g : 𝟙_ V ⟶ Y) (m : X ⊗ Y ⟶ Z) :
    (λ_ (𝟙_ W)).inv ≫ (map F f ⊗ₘ map F g) ≫ μ F X Y ≫ F.map m =
      map F ((λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g) ≫ m) := by
  unfold map
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [μ_natural_assoc]
  rw [tensorHom_def']
  simp only [Category.assoc]
  rw [← leftUnitor_inv_naturality_assoc, left_unitality_inv_assoc]
  rw [← F.map_comp, ← F.map_comp]

end SerrePositivity.LaxPointHom
