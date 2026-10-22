module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：内側の底射の厳密な一致を、二重制限双加群の恒等 underlying 同型へ移す。
方針：底射の等式を除去し、元の制限双加群の恒等同型を取る。
規約：係数対象と underlying 射を保持。使われ方：共通零底の作用比較。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B D : Mon C} (q : A ⟶ B) {f g : B ⟶ D} (h : f = g) (M : Bimod D D)

def bimoduleRestrictionBaseEqIso :
    bimoduleRestrict q (bimoduleRestrict f M) ≅ bimoduleRestrict q (bimoduleRestrict g M) := by
  subst g
  exact Iso.refl _

lemma bimoduleRestrictionBaseEqIso_hom :
    (bimoduleRestrictionBaseEqIso q h M).hom.hom = 𝟙 M.X := by
  subst g
  rfl

lemma bimoduleRestrictionBaseEqIso_inv :
    (bimoduleRestrictionBaseEqIso q h M).inv.hom = 𝟙 M.X := by
  subst g
  rfl

end SerrePositivity.KST.LocalizingInvariants
