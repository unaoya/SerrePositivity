module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftRestriction
public import SerrePositivity.KST.LocalizingInvariants.BimoduleComposition

/-!
概要：異なる底射で制限した二つの双加群の実射を整数 shift する。
方針：制限と shift の恒等 underlying 同型で、元の shift 射を挟む。
規約：元の underlying 射の shift を保持。使われ方：共通底の class 係数逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
variable {R : Type u} [CommRing R] {A B C : Mon (Complex R)}
  (b : A ⟶ B) (c : A ⟶ C) (M : Bimod B B) (N : Bimod C C) (s : ℤ)
  (m : bimoduleRestrict b M ⟶ bimoduleRestrict c N)

def restrictedMap : bimoduleRestrict b (obj M s) ⟶ bimoduleRestrict c (obj N s) :=
  bimoduleComposition (restrictionIso b M s).inv (map m s) (restrictionIso c N s).hom

lemma restrictedMap_hom : (restrictedMap b c M N s m).hom = m.hom⟦s⟧' := by
  change 𝟙 ((bimoduleRestrict b M).X⟦s⟧) ≫ m.hom⟦s⟧' ≫
    𝟙 ((bimoduleRestrict c N).X⟦s⟧) = m.hom⟦s⟧'
  rw [Category.id_comp, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
