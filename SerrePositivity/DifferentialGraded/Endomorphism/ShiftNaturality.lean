module
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftNormalization
public import SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitImage

/-! # 正規化したshift比較の閉零射自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_naturality (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    forward A (x := shiftModule s (ForgetEnrichment.to (Complex A) M))
      (y := shiftModule s (ForgetEnrichment.to (Complex A) N))
      (z := ForgetEnrichment.to (Complex A) N)
      (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f))
      (normalizedModuleShiftOut A D s (ForgetEnrichment.to (Complex A) N)) (zero_add s) =
    forward A (x := shiftModule s (ForgetEnrichment.to (Complex A) M))
      (y := ForgetEnrichment.to (Complex A) M) (z := ForgetEnrichment.to (Complex A) N)
      (normalizedModuleShiftOut A D s (ForgetEnrichment.to (Complex A) M))
      (endomorphismClosedElement A D f) (add_zero s) := by
  apply moduleHomElement_ext A D
  intro x
  have hs : (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x).f 0
        (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f)) =
      Cochain.ofHom ((moduleEvaluation A D x).map ((moduleShiftFunctor A D s).map f)) :=
    endomorphismClosedElement_π A D ((moduleShiftFunctor A D s).map f) x
  rw [moduleHomForward_π, moduleHomForward_π, hs, endomorphismClosedElement_π]
  simp only [zero_mul, mul_zero, Int.negOnePow_zero, one_smul]
  apply Cochain.ext
  intro i j hij
  subst j
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    normalizedModuleShiftOut_v, normalizedModuleShiftOut_v]
  simp only [Cochain.ofHom_v, Category.comp_id, Category.id_comp]
  change (((moduleEvaluation A D x).map (moduleShiftMap A D s f)).f i) = _
  rw [moduleShiftMap_eval]
  rfl

variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma normalizedDGModuleFunctorShiftIso_naturality (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    F.onClosed.map ((moduleShiftFunctor A D s).map f) ≫
        (normalizedDGModuleFunctorShiftIso A D B F s (ForgetEnrichment.to (Complex A) N)).hom =
      (normalizedDGModuleFunctorShiftIso A D B F s (ForgetEnrichment.to (Complex A) M)).hom ≫
        (moduleShiftFunctor A B s).map (F.onClosed.map f) := by
  have h := congrArg (fun z => (F.map
    (shiftModule s (ForgetEnrichment.to (Complex A) M))
    (ForgetEnrichment.to (Complex A) N)).f s z)
      (normalizedModuleShiftOut_naturality A D s f)
  rw [F.map_forward A, F.map_forward A] at h
  have hs : (F.map (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) N))).f 0
        (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f)) =
      endomorphismClosedElement A B (F.onClosed.map ((moduleShiftFunctor A D s).map f)) :=
    dgModuleFunctor_closedElement A D B F ((moduleShiftFunctor A D s).map f)
  rw [hs, dgModuleFunctor_closedElement] at h
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  have hv := congrArg (fun z => ((moduleHomπ A B
    (F.obj (shiftModule s (ForgetEnrichment.to (Complex A) M)))
    (F.obj (ForgetEnrichment.to (Complex A) N)) b).f s z).v i (i + s) rfl) h
  rw [moduleHomForward_π, moduleHomForward_π] at hv
  simp only [zero_mul, mul_zero, Int.negOnePow_zero, one_smul] at hv
  have hπs : (moduleHomπ A B
      (F.obj (shiftModule s (ForgetEnrichment.to (Complex A) M)))
      (F.obj (shiftModule s (ForgetEnrichment.to (Complex A) N))) b).f 0
        (endomorphismClosedElement A B (F.onClosed.map ((moduleShiftFunctor A D s).map f))) =
      Cochain.ofHom ((moduleEvaluation A B b).map
        (F.onClosed.map ((moduleShiftFunctor A D s).map f))) :=
    endomorphismClosedElement_π A B (F.onClosed.map ((moduleShiftFunctor A D s).map f)) b
  have hπ : (moduleHomπ A B (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) N)) b).f 0
        (endomorphismClosedElement A B (F.onClosed.map f)) =
      Cochain.ofHom ((moduleEvaluation A B b).map (F.onClosed.map f)) :=
    endomorphismClosedElement_π A B (F.onClosed.map f) b
  erw [hπs, hπ,
    Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v] at hv
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f]
  change _ = _ ≫ (((moduleEvaluation A B b).map
    (moduleShiftMap A B s (F.onClosed.map f))).f i)
  rw [moduleShiftMap_eval]
  exact hv

/-- 正規化shift比較を閉零加群圏の自然同型に組み立てる。 -/
def normalizedDGModuleFunctorShiftNatIso (s : ℤ) :
    moduleShiftFunctor A D s ⋙ F.onClosed ≅ F.onClosed ⋙ moduleShiftFunctor A B s :=
  NatIso.ofComponents
    (fun M => normalizedDGModuleFunctorShiftIso A D B F s (ForgetEnrichment.to (Complex A) M))
    (fun f => normalizedDGModuleFunctorShiftIso_naturality A D B F s f)

end SerrePositivity.DifferentialGraded
