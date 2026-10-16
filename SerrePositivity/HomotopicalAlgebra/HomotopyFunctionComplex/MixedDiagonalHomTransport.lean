module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHom

/-! # Transport of the mixed action by actual diagram maps -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
variable {C : Type u} [Category.{v} C]

lemma map_id (A : SimplexCategory ⥤ C) (B : SimplexCategory ⥤ Cᵒᵖ) :
    map (𝟙 A) (𝟙 B) = 𝟙 (obj A B) := by
  ext n h
  change 𝟙 _ ≫ h ≫ (𝟙 _).unop = h
  simp only [unop_id, Category.id_comp, Category.comp_id]

lemma map_comp {A₀ A₁ A₂ : SimplexCategory ⥤ C} {B₀ B₁ B₂ : SimplexCategory ⥤ Cᵒᵖ}
    (a : A₁ ⟶ A₀) (a' : A₂ ⟶ A₁) (b : B₁ ⟶ B₀) (b' : B₂ ⟶ B₁) :
    map (a' ≫ a) (b' ≫ b) = map a b ≫ map a' b' := by
  ext n h
  change (a'.app n.unop ≫ a.app n.unop) ≫ h ≫ (b'.app n.unop ≫ b.app n.unop).unop =
    a'.app n.unop ≫ (a.app n.unop ≫ h ≫ (b.app n.unop).unop) ≫ (b'.app n.unop).unop
  simp only [unop_comp, Category.assoc]

lemma action_transport {T : SSet.{v}} {A A' D D' : SimplexCategory ⥤ C}
    {B B' E E' : SimplexCategory ⥤ Cᵒᵖ}
    (a : CosimplicialMapFamily T D A) (a' : CosimplicialMapFamily T D' A')
    (b : CosimplicialMapFamily T E B) (b' : CosimplicialMapFamily T E' B')
    (φ : D' ⟶ D) (k : A ⟶ A') (ψ : E' ⟶ E) (l : B ⟶ B')
    (ha : ∀ n x, a'.app n x = φ.app n.unop ≫ a.app n x ≫ k.app n.unop)
    (hb : ∀ n x, b'.app n x = ψ.app n.unop ≫ b.app n x ≫ l.app n.unop)
    (t : T ⟶ obj A' B') :
    action a' b' t = action a b (t ≫ map k l) ≫ map φ ψ := by
  ext n x
  change a'.app n x ≫ t.app n x ≫ (b'.app n x).unop =
    φ.app n.unop ≫
      (a.app n x ≫ (k.app n.unop ≫ t.app n x ≫ (l.app n.unop).unop) ≫ (b.app n x).unop) ≫
        (ψ.app n.unop).unop
  rw [ha, hb]
  simp only [unop_comp, Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom
