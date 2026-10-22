module

public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftRestriction

/-!
概要：制限した双加群からの元の射を、制限した shift からの実射へ移す。
方針：制限と shift の恒等 underlying 比較の逆を、元の shift 射へ合成する。
規約：元の underlying 射の shift を保持。使われ方：class の右係数標的。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (b : A ⟶ B)
  (M : Bimod B B) (N : Bimod A A) (s : ℤ) (m : bimoduleRestrict b M ⟶ N)

def fromRestriction : bimoduleRestrict b (obj M s) ⟶ obj N s :=
  (restrictionIso b M s).inv ≫ map m s

lemma fromRestriction_hom : (fromRestriction b M N s m).hom = m.hom⟦s⟧' := by
  change 𝟙 ((bimoduleRestrict b M).X⟦s⟧) ≫ m.hom⟦s⟧' = m.hom⟦s⟧'
  exact Category.id_comp _

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
