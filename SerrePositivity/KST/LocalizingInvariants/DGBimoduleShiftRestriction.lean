module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift

/-!
概要：実代数射に沿う双加群の制限と、整数 shift の比較同型を構成する。
方針：同じ shift 複体の恒等射を、tensor–shift 自然性で双加群射にする。
規約：underlying map は恒等。使われ方：Postnikov 層の元の比較射の shift。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
variable {R : Type u} [CommRing R] {A D : Mon (Complex R)} (q : A ⟶ D) (M : Bimod D D)
  (s : ℤ)

def restrictionIso : obj (bimoduleRestrict q M) s ≅ bimoduleRestrict q (obj M s) := by
  refine Bimod.isoOfIso (Iso.refl (M.X⟦s⟧)) ?_ ?_
  · change ((cochainTensorShiftRight A.X M.X s).hom ≫
      ((q.hom ▷ M.X) ≫ M.actLeft)⟦s⟧') ≫ 𝟙 _ =
      (A.X ◁ 𝟙 (M.X⟦s⟧)) ≫
        (q.hom ▷ M.X⟦s⟧) ≫ (cochainTensorShiftRight D.X M.X s).hom ≫ M.actLeft⟦s⟧'
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp, Functor.map_comp,
      Category.assoc]
    rw [tensorShiftRight_naturality_left_assoc]
  · change ((cochainTensorShiftLeft M.X A.X s).hom ≫
      ((M.X ◁ q.hom) ≫ M.actRight)⟦s⟧') ≫ 𝟙 _ =
      (𝟙 (M.X⟦s⟧) ▷ A.X) ≫
        (M.X⟦s⟧ ◁ q.hom) ≫ (cochainTensorShiftLeft M.X D.X s).hom ≫ M.actRight⟦s⟧'
    simp only [Category.comp_id, id_whiskerRight, Category.id_comp, Functor.map_comp,
      Category.assoc]
    rw [tensorShiftLeft_naturality_right_assoc]

lemma restrictionIso_hom : (restrictionIso q M s).hom.hom = 𝟙 (M.X⟦s⟧) := rfl

def mapOver {P : Bimod A A} (f : P ⟶ bimoduleRestrict q M) :
    obj P s ⟶ bimoduleRestrict q (obj M s) := map f s ≫ (restrictionIso q M s).hom

lemma mapOver_hom {P : Bimod A A} (f : P ⟶ bimoduleRestrict q M) :
    (mapOver q M s f).hom = f.hom⟦s⟧' := by
  change f.hom⟦s⟧' ≫ 𝟙 _ = f.hom⟦s⟧'
  exact Category.comp_id _

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
