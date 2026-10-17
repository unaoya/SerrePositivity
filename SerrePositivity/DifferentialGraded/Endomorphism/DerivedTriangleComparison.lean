module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedShiftCoherence
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftNaturalTransformation

/-! # 主K・主導来Hom比較のshift整合性と導来Homの三角性 -/
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

local instance : (endomorphismModuleHom A D E).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
local instance : (endomorphismModuleHom A D E).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A D (EndomorphismObject E) (endomorphismModuleHom A D E)
local instance : (endomorphismDerivedHom A D E hE).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E hE

lemma endomorphismModuleHomHomotopyFac_commShift :
    NatTrans.CommShift (eqToIso (endomorphismModuleHom A D E).onHomotopy_fac).hom ℤ := by
  have he : eqToIso (endomorphismModuleHom A D E).onHomotopy_fac =
      dgModuleFunctorHomotopyFacIso A D (EndomorphismObject E) (endomorphismModuleHom A D E) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rfl
  rw [he]
  exact dgModuleFunctorHomotopyFacIso_commShift A D (EndomorphismObject E)
    (endomorphismModuleHom A D E)

lemma endomorphismDerivedHomHomotopyIso_commShift :
    NatTrans.CommShift (endomorphismDerivedHomHomotopyIso A D E hE).hom ℤ := by
  let := endomorphismModuleHomHomotopyFac_commShift A D E
  let := endomorphismDerivedHomFac_commShift A D E hE
  unfold endomorphismDerivedHomHomotopyIso
  apply quotientNatIsoLift_commShift
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

/-- 実際の主導来Homは、全Hom写像から構成したshift構造について三角関手である。 -/
lemma endomorphismDerivedHomIsTriangulated :
    (endomorphismDerivedHom A D E hE).IsTriangulated := by
  let := dgModuleFunctorHomotopyIsTriangulated A D (EndomorphismObject E)
    (endomorphismModuleHom A D E)
  let := endomorphismDerivedHomHomotopyIso_commShift A D E hE
  exact Functor.isTriangulated_of_precomp_iso
    (endomorphismDerivedHomHomotopyIso A D E hE).symm

end SerrePositivity.DifferentialGraded
