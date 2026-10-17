module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomotopyShiftCoherence
public import SerrePositivity.DifferentialGraded.Module.ConeMaps

/-! # 正規化shift比較と標準coneの連結射 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    forward A (x := ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (y := shiftModule 1 (ForgetEnrichment.to (Complex A) M))
      (z := ForgetEnrichment.to (Complex A) M)
      (endomorphismClosedElement A D (moduleConeConnecting A D f))
      (normalizedModuleShiftOut A D 1 (ForgetEnrichment.to (Complex A) M)) (zero_add 1) =
        -moduleConeFstElement A D f := by
  apply moduleHomElement_ext A D
  intro x
  have hπ : (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (shiftModule 1 (ForgetEnrichment.to (Complex A) M)) x).f 0
        (endomorphismClosedElement A D (moduleConeConnecting A D f)) =
      Cochain.ofHom ((moduleEvaluation A D x).map (moduleConeConnecting A D f)) :=
    endomorphismClosedElement_π A D (moduleConeConnecting A D f) x
  rw [moduleHomForward_π, map_neg, moduleConeFstElement_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  erw [hπ]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    normalizedModuleShiftOut_v_eq, moduleConeConnecting_eval,
    SerrePositivity.coneTriangle_mor₃_f]
  simp only [shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id,
    Preadditive.neg_comp]
  exact congrArg Neg.neg (Cochain.v_comp_XIsoOfEq_hom _ i (i + 1) j rfl hij)

variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma dgModuleFunctorConnecting_eval_f {M N : ModuleCategory A D} (f : M ⟶ N)
    (b : B) (i : ℤ) :
    ((moduleEvaluation A B b).map (F.onClosed.map (moduleConeConnecting A D f) ≫
      (normalizedDGModuleFunctorShiftIso A D B F 1 (ForgetEnrichment.to (Complex A) M)).hom)).f i =
      -(DGFunctor.moduleConeImageFst A D (F.comp (moduleEvaluationDG A B b)) f).v
        i (i + 1) rfl := by
  let G := F.comp (moduleEvaluationDG A B b)
  have h := congrArg (fun z => (G.map
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (ForgetEnrichment.to (Complex A) M)).f 1 z)
      (normalizedModuleShiftOut_connecting A D f)
  rw [G.map_forward_cochain A, map_neg] at h
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  have hc : (G.map (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (shiftModule 1 (ForgetEnrichment.to (Complex A) M))).f 0
      (endomorphismClosedElement A D (moduleConeConnecting A D f)) =
      Cochain.ofHom ((G.toComplexFunctor A).map (moduleConeConnecting A D f)) :=
    G.map_closedElement A (moduleConeConnecting A D f)
  rw [hc] at h
  have hv := Cochain.congr_v h i (i + 1) rfl
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.neg_v] at hv
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f]
  exact hv

lemma dgModuleFunctorConeComparison_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    dgModuleFunctorConeComparison A D B F f ≫ F.onClosed.map (moduleConeConnecting A D f) ≫
      (normalizedDGModuleFunctorShiftIso A D B F 1 (ForgetEnrichment.to (Complex A) M)).hom =
        moduleConeConnecting A B (F.onClosed.map f) := by
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgModuleFunctorConnecting_eval_f, dgModuleFunctorConeComparison_eval,
    moduleConeConnecting_eval, SerrePositivity.coneTriangle_mor₃_f]
  simp only [Preadditive.comp_neg, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  let G := F.comp (moduleEvaluationDG A B b)
  exact congrArg Neg.neg (complexConeDesc_fst A ((G.toComplexFunctor A).map f)
    (DGFunctor.moduleConeImageInl A D G f)
    ((G.toComplexFunctor A).map (moduleConeInr A D f))
    (DGFunctor.moduleConeImageFst A D G f) (DGFunctor.moduleConeImageInl_d A D G f)
    (DGFunctor.moduleConeImage_inl_fst A D G f)
    (DGFunctor.moduleConeImage_inr_fst A D G f) i)

end SerrePositivity.DifferentialGraded
