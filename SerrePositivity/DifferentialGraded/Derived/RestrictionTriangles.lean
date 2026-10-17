module
public import SerrePositivity.DifferentialGraded.Derived.RestrictionShift
public import SerrePositivity.DifferentialGraded.Derived.Triangulated
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftNaturalTransformation

/-! # 主K経由の制限と導来制限のshift整合的比較・三角性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- dg制限を主Kで適用する経路と、主導来制限の自然な正方形。 -/
def dgDerivedRestrictionHomotopyIso :
    (dgModuleRestriction A D E F.op).onHomotopy ⋙ moduleHomotopyToDerivedClosed A D ≅
      moduleHomotopyToDerivedClosed A E ⋙ dgDerivedRestriction A D E F :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A E))
    ((Functor.associator (moduleToHomotopy A E) (dgModuleRestriction A D E F.op).onHomotopy
        (moduleHomotopyToDerivedClosed A D)).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (dgModuleRestriction A D E F.op).onHomotopy_fac)
        (moduleHomotopyToDerivedClosed A D) ≪≫
      Functor.associator (dgModuleRestriction A D E F.op).onClosed
        (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D) ≪≫
      Functor.isoWhiskerLeft (dgModuleRestriction A D E F.op).onClosed
        (moduleToHomotopyDerivedIso A D) ≪≫
      (eqToIso (dgDerivedRestriction_enriched_fac A D E F)).symm ≪≫
      Functor.isoWhiskerRight (moduleToHomotopyDerivedIso A E).symm
        (dgDerivedRestriction A D E F) ≪≫
      Functor.associator (moduleToHomotopy A E) (moduleHomotopyToDerivedClosed A E)
        (dgDerivedRestriction A D E F))

local instance : (dgModuleRestriction A D E F.op).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A E D (dgModuleRestriction A D E F.op)
local instance : (dgModuleRestriction A D E F.op).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A E D (dgModuleRestriction A D E F.op)
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F

lemma dgModuleRestrictionHomotopyFac_commShift :
    NatTrans.CommShift (eqToIso (dgModuleRestriction A D E F.op).onHomotopy_fac).hom ℤ := by
  have he : eqToIso (dgModuleRestriction A D E F.op).onHomotopy_fac =
      dgModuleFunctorHomotopyFacIso A E D (dgModuleRestriction A D E F.op) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rfl
  rw [he]
  exact dgModuleFunctorHomotopyFacIso_commShift A E D (dgModuleRestriction A D E F.op)

lemma dgDerivedRestrictionHomotopyIso_commShift :
    NatTrans.CommShift (dgDerivedRestrictionHomotopyIso A D E F).hom ℤ := by
  let := dgModuleRestrictionHomotopyFac_commShift A D E F
  let := dgDerivedRestrictionFac_commShift A D E F
  unfold dgDerivedRestrictionHomotopyIso
  apply quotientNatIsoLift_commShift
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

lemma dgDerivedRestrictionIsTriangulated : (dgDerivedRestriction A D E F).IsTriangulated := by
  let := dgModuleFunctorHomotopyIsTriangulated A E D (dgModuleRestriction A D E F.op)
  let := dgDerivedRestrictionHomotopyIso_commShift A D E F
  exact Functor.isTriangulated_of_precomp_iso (dgDerivedRestrictionHomotopyIso A D E F).symm

lemma dgDerivedRestriction_additive : (dgDerivedRestriction A D E F).Additive := by
  rw [Localization.functor_additive_iff (moduleHomotopyToDerivedClosed A E)
    (moduleHomotopyQuasiIso A E)]
  exact Functor.additive_of_iso (dgDerivedRestrictionHomotopyIso A D E F)

end SerrePositivity.DifferentialGraded
