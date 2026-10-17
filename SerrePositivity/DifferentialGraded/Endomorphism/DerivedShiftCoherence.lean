module
public import SerrePositivity.DifferentialGraded.Endomorphism.ConeTriangleComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomHomotopyComparison

/-! # 導来Homの整合的shift比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

instance endomorphismDerivedHomLifting :
    Localization.Lifting (moduleToDerived A D) (moduleQuasiIso A D)
      ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
      (endomorphismDerivedHom A D E hE) :=
  ⟨eqToIso (endomorphismDerivedHom_fac A D E hE)⟩

/-- 導来Homのshift構造。全Hom写像の正規化比較とzero/add coherenceを局所化する。 -/
@[instance_reducible]
def endomorphismDerivedHomCommShift : (endomorphismDerivedHom A D E hE).CommShift ℤ := by
  letI := dgModuleFunctorCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
  exact Functor.commShiftOfLocalization (moduleToDerived A D) (moduleQuasiIso A D) ℤ
    ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
    (endomorphismDerivedHom A D E hE)

section
local instance : (endomorphismModuleHom A D E).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE

lemma endomorphismDerivedHomFac_commShift :
    NatTrans.CommShift (eqToIso (endomorphismDerivedHom_fac A D E hE)).hom ℤ := by
  change NatTrans.CommShift
    (Localization.Lifting.iso (moduleToDerived A D) (moduleQuasiIso A D)
      ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
      (endomorphismDerivedHom A D E hE)).hom ℤ
  exact NatTrans.commShift_iso_hom_of_localization (moduleToDerived A D)
    (moduleQuasiIso A D) ℤ
    ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
    (endomorphismDerivedHom A D E hE)

end
end SerrePositivity.DifferentialGraded
