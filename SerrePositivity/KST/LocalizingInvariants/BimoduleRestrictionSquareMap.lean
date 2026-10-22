module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：底の可換正方形に沿う、二段の制限双加群の元の射を構成する。
方針：元の係数射の作用保存と底の厳密な合成式を tensor の関手則へ送る。
規約：underlying 射を取り替えない。使われ方：係数像の正方形に沿う自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B A' B' : Mon C} (f : A ⟶ B) (f' : A' ⟶ B') (s : A ⟶ A') (t : B ⟶ B')
  (h : f ≫ t = s ≫ f') {M : Bimod B B} {N : Bimod B' B'} (m : M ⟶ bimoduleRestrict t N)

def bimoduleRestrictSquareMap : bimoduleRestrict f M ⟶
    bimoduleRestrict s (bimoduleRestrict f' N) where
  hom := m.hom
  left_act_hom := by
    let l : M.X ⟶ N.X := m.hom
    have hm : M.actLeft ≫ l = (t.hom ⊗ₘ l) ≫ N.actLeft := by
      have e := m.left_act_hom
      change M.actLeft ≫ l = (B.X ◁ l) ≫ (t.hom ▷ N.X) ≫ N.actLeft at e
      rw [← tensorHom_def'_assoc] at e
      exact e
    have he : f.hom ≫ t.hom = s.hom ≫ f'.hom := congrArg Mon.Hom.hom h
    change ((f.hom ▷ M.X) ≫ M.actLeft) ≫ l =
      (A.X ◁ l) ≫ (s.hom ▷ N.X) ≫ (f'.hom ▷ N.X) ≫ N.actLeft
    rw [Category.assoc, hm]
    simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id, he]
  right_act_hom := by
    let l : M.X ⟶ N.X := m.hom
    have hm : M.actRight ≫ l = (l ⊗ₘ t.hom) ≫ N.actRight := by
      have e := m.right_act_hom
      change M.actRight ≫ l = (l ▷ B.X) ≫ (N.X ◁ t.hom) ≫ N.actRight at e
      rw [← tensorHom_def_assoc] at e
      exact e
    have he : f.hom ≫ t.hom = s.hom ≫ f'.hom := congrArg Mon.Hom.hom h
    change ((M.X ◁ f.hom) ≫ M.actRight) ≫ l =
      (l ▷ A.X) ≫ (N.X ◁ s.hom) ≫ (N.X ◁ f'.hom) ≫ N.actRight
    rw [Category.assoc, hm]
    simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id, he]

lemma bimoduleRestrictSquareMap_hom : (bimoduleRestrictSquareMap f f' s t h m).hom = m.hom := rfl

end SerrePositivity.KST.LocalizingInvariants
