module
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftNaturality

/-! # 正規化shift比較と零shiftの整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_zero (M : RightModule A D) :
    normalizedModuleShiftOut A D 0 M =
      endomorphismClosedElement A D (moduleShiftZeroIsoObj A D M).hom := by
  apply moduleHomElement_ext A D
  intro x
  have hπ : (moduleHomπ A D (shiftModule 0 M) M x).f 0
      (endomorphismClosedElement A D (moduleShiftZeroIsoObj A D M).hom) =
      Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftZeroIsoObj A D M).hom) :=
    endomorphismClosedElement_π A D (moduleShiftZeroIsoObj A D M).hom x
  erw [hπ]
  apply Cochain.ext₀
  intro i
  rw [Cochain.ofHom_v, moduleShiftZeroIsoObj_hom_eval, shiftFunctorZero_hom_app_f]
  rw [← Cochain.v_comp_XIsoOfEq_hom _ i (i + 0) i rfl (add_zero i),
    normalizedModuleShiftOut_v, Category.id_comp]

variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma normalizedDGModuleFunctorShiftNatIso_zero :
    normalizedDGModuleFunctorShiftNatIso A D B F 0 =
      CategoryTheory.Functor.CommShift.isoZero F.onClosed ℤ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  change ((moduleEvaluation A B b).map
    (normalizedDGModuleFunctorShiftIso A D B F 0 (ForgetEnrichment.to (Complex A) M)).hom).f i = _
  rw [normalizedDGModuleFunctorShiftIso_hom_eval_f, normalizedModuleShiftOut_zero]
  have hm : (F.map (shiftModule 0 (ForgetEnrichment.to (Complex A) M))
      (ForgetEnrichment.to (Complex A) M)).f 0
      (endomorphismClosedElement A D
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom) =
      endomorphismClosedElement A B (F.onClosed.map
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom) :=
    dgModuleFunctor_closedElement A D B F _
  erw [hm]
  have hπ : (moduleHomπ A B (F.obj (shiftModule 0 (ForgetEnrichment.to (Complex A) M)))
      (F.obj (ForgetEnrichment.to (Complex A) M)) b).f 0
      (endomorphismClosedElement A B (F.onClosed.map
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom)) =
      Cochain.ofHom ((moduleEvaluation A B b).map (F.onClosed.map
        (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom)) :=
    endomorphismClosedElement_π A B _ b
  erw [hπ]
  change (Cochain.ofHom ((moduleEvaluation A B b).map (F.onClosed.map
    (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom))).v i (i + 0) rfl = _
  rw [← Cochain.v_comp_XIsoOfEq_inv _ i i (i + 0) (add_zero i) (add_zero i),
    Cochain.ofHom_v]
  simp only [CategoryTheory.Functor.CommShift.isoZero_hom_app,
    CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
  change _ =
    ((moduleEvaluation A B b).map (F.onClosed.map
      (moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M)).hom)).f i ≫
      ((moduleEvaluation A B b).map
        (moduleShiftZeroIsoObj A B (F.obj (ForgetEnrichment.to (Complex A) M))).inv).f i
  rw [moduleShiftZeroIsoObj_inv_eval, shiftFunctorZero_inv_app_f]
  rfl

end SerrePositivity.DifferentialGraded
