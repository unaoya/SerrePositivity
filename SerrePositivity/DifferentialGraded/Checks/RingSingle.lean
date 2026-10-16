module
public import SerrePositivity.DifferentialGraded.Perfect.RingSingleShift
public import Mathlib.Data.ZMod.Basic

/-! # 有限射影項の全整数次数でのperfect性と有限和閉性の監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)
    (X : Fin 3 → DerivedModuleCategory A D) (hX : ∀ j, modulePerfectOver A D S (X j)) :
    modulePerfectOver A D S (⨁ X) := modulePerfectOver_biproduct A D S X hX
example (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)
    (F : ModuleCat.{u} A ⥤ DerivedModuleCategory A D) [F.Additive]
    (hA : modulePerfectOver A D S (F.obj (ModuleCat.of A A)))
    (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] :
    modulePerfectOver A D S (F.obj M) := modulePerfectOver_image_finiteProjective A D S F hA M
example (n : ℤ) (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] :
    modulePerfect A PUnit.{1} ((ringSingleToDerived A n).obj M) :=
  ringSingleToDerived_finiteProjective_perfect A n M
example : modulePerfect (ZMod 2) PUnit.{1}
    ((ringSingleToDerived (ZMod 2) (-3)).obj (ModuleCat.of (ZMod 2) (ZMod 2))) :=
  ringSingleToDerived_unit_perfect (ZMod 2) (-3)
example : modulePerfect (ZMod 2) PUnit.{1}
    ((ringSingleToDerived (ZMod 2) 2).obj (ModuleCat.of (ZMod 2) (ZMod 2))) :=
  ringSingleToDerived_unit_perfect (ZMod 2) 2

#print axioms modulePerfectOver_biproduct
#print axioms modulePerfectOver_image_finiteProjective
#print axioms complexToRingModule
#print axioms complexToRingModuleAdditive
#print axioms ringModule_unit_eq_representable
#print axioms ringSingleZeroToDerived
#print axioms ringSingleZeroToDerivedAdditive
#print axioms ringSingleZeroToDerived_unit_perfect
#print axioms ringSingleZeroToDerived_finiteProjective_perfect
#print axioms ringModule_shift_eq
#print axioms complexToRingModuleShiftObjIso
#print axioms ringSingleToDerived
#print axioms ringSingleToDerivedAdditive
#print axioms ringSingleToDerived_unit_perfect
#print axioms ringSingleToDerived_finiteProjective_perfect
