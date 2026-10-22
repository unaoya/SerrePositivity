module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：実双加群の二段の底制限と合成による制限を、恒等 underlying 射で比較する。
方針：作用の二つの合成を tensor の関手則で一致させる。
規約：元の双加群を取り替えない。使われ方：平方零代数の底変更と derivation。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A B D : Mon C}
  (a : A ⟶ B) (b : B ⟶ D) (N : Bimod D D)

def bimoduleRestrictionCompIso : bimoduleRestrict (a ≫ b) N ≅
    bimoduleRestrict a (bimoduleRestrict b N) := by
  refine Bimod.isoOfIso (Iso.refl N.X) ?_ ?_
  · change (((a.hom ≫ b.hom) ▷ N.X) ≫ N.actLeft) ≫ 𝟙 N.X =
      (A.X ◁ 𝟙 N.X) ≫ (a.hom ▷ N.X) ≫ (b.hom ▷ N.X) ≫ N.actLeft
    simp only [comp_whiskerRight, Category.assoc, Category.comp_id, whiskerLeft_id,
      Category.id_comp]
  · change ((N.X ◁ (a.hom ≫ b.hom)) ≫ N.actRight) ≫ 𝟙 N.X =
      (𝟙 N.X ▷ A.X) ≫ (N.X ◁ a.hom) ≫ (N.X ◁ b.hom) ≫ N.actRight
    simp only [whiskerLeft_comp, Category.assoc, Category.comp_id, id_whiskerRight,
      Category.id_comp]

lemma bimoduleRestrictionCompIso_hom : (bimoduleRestrictionCompIso a b N).hom.hom = 𝟙 N.X := rfl

end SerrePositivity.KST.LocalizingInvariants
