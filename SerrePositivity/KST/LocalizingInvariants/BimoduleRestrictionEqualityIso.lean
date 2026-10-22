module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：等しい底射に沿う一重制限双加群の、underlying 恒等射を持つ同型。
方針：底射の等式を除去して恒等同型を取る。
規約：係数対象と射を保持。使われ方：元の共通底での零底係数比較。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : Mon C} {f g : A ⟶ B} (h : f = g) (M : Bimod B B)

def bimoduleRestrictBaseEqIso : bimoduleRestrict f M ≅ bimoduleRestrict g M := by
  subst g
  exact Iso.refl _

lemma bimoduleRestrictBaseEqIso_hom :
    (bimoduleRestrictBaseEqIso h M).hom.hom = 𝟙 M.X := by
  subst g
  rfl

lemma bimoduleRestrictBaseEqIso_inv :
    (bimoduleRestrictBaseEqIso h M).inv.hom = 𝟙 M.X := by
  subst g
  rfl

end SerrePositivity.KST.LocalizingInvariants
