module

public import SerrePositivity.KST.LocalizingInvariants.ConcentratedComplexHomology
public import SerrePositivity.KST.LocalizingInvariants.ProFullSubcategoryLift
public import SerrePositivity.KST.LocalizingInvariants.ProModuleReflection

/-!
概要：単一の整数次数に厳密集中した層の群の pro 同型を、元の複体の実 pro 逆へ戻す。
方針：群の逆を加群へ補正し、集中複体上のホモロジーの圏同値で反映する。
規約：ホモロジー集中だけでは適用しない。使われ方：Postnikov 層の実逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable (R : Type u) [CommRing R] (d : ℤ) {X Y : Tower (Complex R)} (f : LevelHom X Y)
  (hX : ∀ i, concentratedComplexProperty R d (X.obj i))
  (hY : ∀ i, concentratedComplexProperty R d (Y.obj i))

include hX hY in
lemma proIso_of_concentratedComplex_homology
    (hf : IsProIso (f.map (homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) d))) :
    IsProIso f := by
  let a := fullSubcategoryLevelHom (concentratedComplexProperty R d) hX f hY
  have ha : IsProIso (a.map (concentratedComplexHomology R d)) := hf
  have hi := proIso_of_fullyFaithful (concentratedComplexHomology R d) a ha
  exact hi.map (concentratedComplexProperty R d).ι

include hX hY in
lemma proIso_of_concentratedComplex_groups
    (hf : IsProIso (f.map (DGAlgebra.complexGroups R (-d)))) : IsProIso f := by
  apply proIso_of_concentratedComplex_homology R d f hX hY
  apply proIso_of_module_groups R (f.map (homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) d))
  change IsProIso (f.map (homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (-(-d)) ⋙
    forget₂ (ModuleCat R) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp)) at hf
  rw [neg_neg] at hf
  exact hf

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
