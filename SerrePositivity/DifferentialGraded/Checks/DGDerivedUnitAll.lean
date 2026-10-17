module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionUnitAll
public import Mathlib.Data.ZMod.Basic

/-! # 導来制限の三角性・余積保存と全対象の導来単位 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

example : letI := dgDerivedRestrictionCommShift A D E F
    (dgDerivedRestriction A D E F).IsTriangulated := dgDerivedRestrictionIsTriangulated A D E F

example : letI := dgDerivedRestrictionCommShift A D E F
    letI := dgDerivedExtensionCommShift A D E F
    NatTrans.CommShift (dgDerivedExtensionUnit A D E F) ℤ :=
  dgDerivedExtensionUnit_commShift A D E F

example (J : Type u) : PreservesColimitsOfShape (Discrete J) (dgDerivedRestriction A D E F) :=
  inferInstance

example {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    moduleCompact A E ((dgDerivedExtension A D E F).obj X) := dgDerivedExtension_compact A D E F hX

-- 本質的全射性・Hom flatness・有界性を要求せず、任意の導来対象で判定する。
example (hF : HomQuasiIso F) (X : DerivedModuleCategory A D) :
    IsIso ((dgDerivedExtensionUnit A D E F).app X) := dgDerivedExtensionUnit_isIso_all A D E F hF X

example (hF : HomQuasiIso F) : (dgDerivedExtension A D E F).FullyFaithful :=
  dgDerivedExtensionFullyFaithful A D E F hF

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) (hF : HomQuasiIso F)
    (M : DerivedModuleCategory (ZMod 2) X) :
    IsIso ((dgDerivedExtensionUnit (ZMod 2) X Y F).app M) :=
  dgDerivedExtensionUnit_isIso_all (ZMod 2) X Y F hF M

namespace SerrePositivity.DifferentialGraded
#print axioms dgDerivedRestriction_enriched_fac
#print axioms dgDerivedRestriction_enriched_lifting
#print axioms dgDerivedRestrictionCommShift
#print axioms dgDerivedRestrictionFac_commShift
#print axioms dgDerivedRestrictionHomotopyIso
#print axioms dgModuleRestrictionHomotopyFac_commShift
#print axioms dgDerivedRestrictionHomotopyIso_commShift
#print axioms dgDerivedRestrictionIsTriangulated
#print axioms dgDerivedRestriction_additive
#print axioms dgDerivedExtensionCommShift
#print axioms dgDerivedExtensionRestrictionAdjunction_commShift
#print axioms dgDerivedExtensionUnit_commShift
#print axioms dgDerivedExtensionCounit_commShift
#print axioms dgDerivedExtensionIsTriangulated
#print axioms dgDerivedExtension_additive
#print axioms dgDerivedExtension_perfect
#print axioms dgDerivedExtension_compact
#print axioms derivedAdjunction_sigmaComparison_projection
#print axioms derivedAdjunction_sigmaHom_injective
#print axioms derivedAdjunction_sigmaHom_surjective
#print axioms derivedAdjunction_sigmaComparison_isIso
#print axioms derivedAdjunction_rightAdjoint_preservesCoproduct
#print axioms derivedNatTransIsoLocus_stableUnderRetracts
#print axioms dgDerivedRestriction_preservesCoproduct
#print axioms dgDerivedRestriction_preservesCoproductsOfShape
#print axioms dgDerivedExtensionUnit_isIso_onPerfect
#print axioms dgDerivedExtensionUnit_isIso_all
#print axioms dgDerivedExtensionFullyFaithful
end SerrePositivity.DifferentialGraded
