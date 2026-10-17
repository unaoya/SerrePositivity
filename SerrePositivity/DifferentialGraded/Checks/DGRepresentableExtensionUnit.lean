module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentableUnit
public import Mathlib.Data.ZMod.Basic

/-! # graph延長–制限単位の代表加群計算と可逆性 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

example (d : D) : functorExtensionUnit A D E F (representable A d) ≫
    (moduleRestriction A D E F.op).map (dgModuleExtensionRepresentableIso A D E F d).hom =
      representableRestrictionMap A D E F d := functorExtensionUnit_representable A D E F d

-- Hom準同型性だけを仮定し、本質的全射性・Hom flatness・有界性を要求しない。
example (hF : HomQuasiIso F) (d : D) :
    IsIso ((dgDerivedExtensionUnit A D E F).app
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)))) :=
  dgDerivedExtensionUnit_representable_isIso A D E F hF d

example (M : ModuleCategory A D) :
    (dgModuleEnrichedRestrictionAdjunction A D E F).unit.app M =
      functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) :=
  dgModuleEnrichedRestrictionAdjunction_unit A D E F M

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) (hF : HomQuasiIso F) (x : X) :
    IsIso ((dgDerivedExtensionUnit (ZMod 2) X Y F).app
      ((moduleToDerived (ZMod 2) X).obj
        (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) x)))) :=
  dgDerivedExtensionUnit_representable_isIso (ZMod 2) X Y F hF x

namespace SerrePositivity.DifferentialGraded
#print axioms functorExtensionUnit_representable
#print axioms functorExtensionUnit_representable_quasiIso
#print axioms dgModuleExtensionRestrictionAdjunction_unit
#print axioms dgModuleEnrichedRestrictionAdjunction_unit
#print axioms dgDerivedExtensionRestrictionAdjunction_homEquiv
#print axioms dgDerivedExtensionUnit_computation
#print axioms functorExtensionUnit_resolution_quasiIso
#print axioms dgDerivedExtensionUnit_representable_isIso
#print axioms dgModuleEnrichedRestrictionAdjunction
end SerrePositivity.DifferentialGraded
