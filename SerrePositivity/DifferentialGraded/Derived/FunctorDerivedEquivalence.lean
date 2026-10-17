module
public import SerrePositivity.DifferentialGraded.Derived.RestrictionConservative
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionUnitAll

/-! # dg準同値に沿う実際の導来延長–制限同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtensionCounit_isIso_all (hF : QuasiEquivalence F) (X : DerivedModuleCategory A E) :
    IsIso ((dgDerivedExtensionCounit A D E F).app X) := by
  let adj := dgDerivedExtensionRestrictionAdjunction A D E F
  let R := dgDerivedRestriction A D E F
  have hu : IsIso (adj.unit.app (R.obj X)) := dgDerivedExtensionUnit_isIso_all A D E F hF.1 _
  let := hu
  have he : R.map (adj.counit.app X) = inv (adj.unit.app (R.obj X)) := by
    apply (cancel_epi (adj.unit.app (R.obj X))).1
    rw [adj.right_triangle_components, IsIso.hom_inv_id]
    rfl
  have hm : IsIso (R.map (adj.counit.app X)) := by rw [he]; infer_instance
  let := hm
  exact dgDerivedRestriction_reflectsIso A D E F hF.2 (adj.counit.app X)

/-- 各Homの準同型と主Kの本質的全射性から、全右加群の主導来圏の同値を構成する。 -/
def dgFunctorDerivedEquivalence (hF : QuasiEquivalence F) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  letI (X : DerivedModuleCategory A D) :
      IsIso ((dgDerivedExtensionRestrictionAdjunction A D E F).unit.app X) :=
    dgDerivedExtensionUnit_isIso_all A D E F hF.1 X
  letI (Y : DerivedModuleCategory A E) :
      IsIso ((dgDerivedExtensionRestrictionAdjunction A D E F).counit.app Y) :=
    dgDerivedExtensionCounit_isIso_all A D E F hF Y
  exact (dgDerivedExtensionRestrictionAdjunction A D E F).toEquivalence

lemma dgFunctorDerivedEquivalence_functor (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).functor = dgDerivedExtension A D E F := rfl

lemma dgFunctorDerivedEquivalence_inverse (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).inverse = dgDerivedRestriction A D E F := rfl

lemma dgFunctorDerivedEquivalence_unit (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom = dgDerivedExtensionUnit A D E F := rfl

lemma dgFunctorDerivedEquivalence_counit (hF : QuasiEquivalence F) :
    (dgFunctorDerivedEquivalence A D E F hF).counitIso.hom = dgDerivedExtensionCounit A D E F := rfl

end SerrePositivity.DifferentialGraded
