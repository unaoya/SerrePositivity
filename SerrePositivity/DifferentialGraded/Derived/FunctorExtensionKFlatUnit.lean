module
public import SerrePositivity.DifferentialGraded.Derived.FunctorDerivedEquivalence
public import SerrePositivity.DifferentialGraded.Derived.Evaluation
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComparison
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveKFlat

/-! # 相対K-flat右加群上の延長単位と準同値に沿う制限の準同型反映 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- graph延長は右相対K-flat加群間の準同型を保つ。 -/
lemma dgModuleExtension_relativeKFlat_quasiIso {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((dgModuleExtension A D E F).onClosed.map f) := by
  intro e
  rw [dgModuleExtension_map_eval]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A D
    ((functorGraph A D E F).leftAt e) hM hN f hf

/-- Hom準同型に沿う単位は標準の射影解像度上で準同型。 -/
lemma functorExtensionUnit_canonical_quasiIso (hF : HomQuasiIso F) (M : ModuleCategory A D) :
    moduleQuasiIso A D (functorExtensionUnit A D E F
      (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)) := by
  let P := moduleCanonicalProjectiveResolution A D M
  let i := moduleDerivedIso A D P.π P.quasiIso
  let c := dgDerivedRestrictionComputation A D E F
    ((dgModuleExtension A D E F).onClosed.obj P.obj)
  let η := functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) P.obj)
  have hu := dgDerivedExtensionUnit_isIso_all A D E F hF ((moduleToDerived A D).obj M)
  let := hu
  have h := dgDerivedExtensionUnit_computation A D E F M
  have hc : IsIso (i.inv ≫ (moduleToDerived A D).map η ≫ c.inv) := by
    rw [← h]
    infer_instance
  let := hc
  have ht : IsIso ((moduleToDerived A D).map η ≫ c.inv) :=
    IsIso.of_isIso_comp_left i.inv _
  let := ht
  exact (moduleToDerived_map_isIso_iff A D η).mp
    (IsIso.of_isIso_comp_right ((moduleToDerived A D).map η) c.inv)

/-- Hom準同型に沿う実際の単位は任意の右相対K-flat加群上で準同型。 -/
lemma functorExtensionUnit_relativeKFlat_quasiIso (hF : HomQuasiIso F)
    (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    moduleQuasiIso A D (functorExtensionUnit A D E F
      (ForgetEnrichment.to (Complex A) M)) := by
  let P := moduleCanonicalProjectiveResolution A D M
  have hP := moduleHomotopicallyProjective_relativeKFlat A D P.projective
  have he := dgModuleExtension_relativeKFlat_quasiIso A D E F hP hM P.π P.quasiIso
  have hr := moduleRestriction_quasiIso A D E F.op _ he
  have hu := functorExtensionUnit_canonical_quasiIso A D E F hF M
  have hn := (dgModuleUnit A D E F).naturality P.π
  change P.π ≫ functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) =
    functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) P.obj) ≫
      (moduleRestriction A D E F.op).map ((dgModuleExtension A D E F).onClosed.map P.π) at hn
  have hc := (moduleQuasiIso A D).comp_mem _ _ hu hr
  rw [← hn] at hc
  exact (moduleQuasiIso A D).of_precomp _ _ P.quasiIso hc

/-- 本質的全射なdg関手の制限は、全右加群射の準同型性を反映する。 -/
lemma moduleRestriction_reflects_quasiIso (hF : F.onHomotopy.EssSurj)
    {M N : ModuleCategory A E} (f : M ⟶ N)
    (hf : moduleQuasiIso A D ((moduleRestriction A D E F.op).map f)) :
    moduleQuasiIso A E f := by
  have hi := moduleToDerived_inverts A D _ hf
  have hi' : IsIso ((moduleToDerived A E ⋙ dgDerivedRestriction A D E F).map f) := by
    rw [dgDerivedRestriction_fac]
    exact hi
  have : IsIso ((dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f)) := hi'
  exact (moduleToDerived_map_isIso_iff A E f).mp
    (dgDerivedRestriction_reflectsIso A D E F hF ((moduleToDerived A E).map f))

/-- 制限への指定射を閉零の延長–制限随伴で転置した実際の加群射。 -/
def functorExtensionTranspose {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) :
    (dgModuleExtension A D E F).onClosed.obj R ⟶ M :=
  ((dgModuleExtensionRestrictionAdjunction A D E F).homEquiv R M).symm q

lemma functorExtensionTranspose_eq {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) :
    functorExtensionTranspose A D E F q =
      (dgModuleExtension A D E F).onClosed.map q ≫
        functorExtensionCounit A D E F (ForgetEnrichment.to (Complex A) M) :=
  (dgModuleExtensionRestrictionAdjunction A D E F).homEquiv_counit _ _ q

lemma functorExtensionTranspose_unit_fac {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) :
    functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) R) ≫
        (moduleRestriction A D E F.op).map (functorExtensionTranspose A D E F q) = q :=
  ((dgModuleExtensionRestrictionAdjunction A D E F).homEquiv_unit _ _
    (functorExtensionTranspose A D E F q)).symm.trans
      (Equiv.apply_symm_apply _ q)

/-- 準同値に沿い、制限への右K-flat準同型を転置すると再び準同型になる。 -/
lemma functorExtensionTranspose_quasiIso (hF : QuasiEquivalence F)
    {R : ModuleCategory A D} {M : ModuleCategory A E}
    (hR : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) R))
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) (hq : moduleQuasiIso A D q) :
    moduleQuasiIso A E (functorExtensionTranspose A D E F q) := by
  apply moduleRestriction_reflects_quasiIso A D E F hF.2
  have hu := functorExtensionUnit_relativeKFlat_quasiIso A D E F hF.1 R hR
  have hc : moduleQuasiIso A D
      (functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) R) ≫
        (moduleRestriction A D E F.op).map (functorExtensionTranspose A D E F q)) := by
    rw [functorExtensionTranspose_unit_fac]
    exact hq
  exact (moduleQuasiIso A D).of_precomp _ _ hu hc

end SerrePositivity.DifferentialGraded
