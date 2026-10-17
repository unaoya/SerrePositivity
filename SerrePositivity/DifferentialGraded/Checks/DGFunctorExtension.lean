module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Module.FunctorGraphActions
public import Mathlib.Data.ZMod.Basic

/-! # graph tensorの導来延長・代表加群比較・独立宇宙の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

-- 元のHomのflatness・有界性なし。全加群型のsmallnessも要求しない。
example : DGFunctor A (RightModule A D) (RightModule A E) := dgModuleExtension A D E F

example {M : ModuleCategory A D} (P : ModuleProjectiveResolution A D M) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj P.obj) :=
  dgDerivedExtensionResolutionComputation A D E F P

example (hF : HomQuasiIso F) (d : D) :
    (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)) ≅
      (dgDerivedRestriction A D E F).obj ((dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d)))) :=
  dgDerivedRoundTripRepresentableIso A D E F hF d

-- graphの作用比較はsource対象型のsmallnessを使わない。
example (X : Type v) [DGCategory A X] (F : DGFunctor A X E) (e : E) :
    (functorGraph A X E F).leftAt e = F.comp (leftRepresentable A e) :=
  functorGraph_leftAt A X E F e

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) (x : X) :
    (dgDerivedExtension (ZMod 2) X Y F).obj
        ((moduleToDerived (ZMod 2) X).obj
          (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) x))) ≅
      (moduleToDerived (ZMod 2) Y).obj
        (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) (F.obj x))) :=
  dgDerivedExtensionRepresentableIso (ZMod 2) X Y F x

example {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((dgModuleExtension A D E F).onClosed.map f) :=
  dgModuleExtension_projective_quasiIso A D E F hM hN f hf

namespace SerrePositivity.DifferentialGraded
#print axioms dgModuleFunctor_projective_quasiIso
#print axioms functorGraph
#print axioms functorGraph_value
#print axioms dgModuleExtension
#print axioms dgModuleExtension_value
#print axioms dgModuleExtensionRepresentableIso
#print axioms representableRestriction_naturality
#print axioms representableRestrictionMap
#print axioms representableRestrictionMap_eval
#print axioms representableRestrictionMap_quasiIso
#print axioms dgExtensionHomotopyToDerived
#print axioms dgResolutionDerivedExtension
#print axioms dgDerivedExtension
#print axioms dgExtensionHomotopyComputation
#print axioms dgResolutionDerivedExtensionComputation
#print axioms dgResolutionDerivedExtensionIso
#print axioms dgResolutionDerivedExtensionIso_self
#print axioms dgResolutionDerivedExtensionIso_trans
#print axioms dgDerivedExtensionResolutionComputation
#print axioms dgModuleExtension_projective_quasiIso
#print axioms moduleIdentityProjectiveResolution
#print axioms dgDerivedExtensionRepresentableIso
#print axioms representableDerivedRestrictionIso
#print axioms dgDerivedRoundTripRepresentableIso
#print axioms functorGraph_leftAt
#print axioms dgModuleExtensionValueIso
end SerrePositivity.DifferentialGraded
