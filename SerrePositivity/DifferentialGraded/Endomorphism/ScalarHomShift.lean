module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomElements
public import SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonShift
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomHomotopyRetracts

/-! # 係数変更した全次数Homの反変shift表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarBaseChange_compose {D : Type v} [DGCategory A D]
    {x y z : D} {p q n : ℤ} (g : GradedHom A y z q) (f : GradedHom A x y p)
    (h : p + q = n) :
    let := φ.toAlgebra
    compose A' (D := ScalarExtension.DGBaseChange φ D)
      (x := x) (y := y) (z := z) ((1 : A') ⊗ₜ[A] g) ((1 : A') ⊗ₜ[A] f) h =
      (1 : A') ⊗ₜ[A] compose A g f h := by
  let := φ.toAlgebra
  unfold compose
  rw [scalarBaseChange_forward]
  simp only [Units.smul_def]
  exact (map_zsmul (TensorProduct.mk A A' _ (1 : A'))
    ((p * q).negOnePow : ℤ) (forward A f g h)).symm

variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D))ᵒᵖ (Complex A'))

def scalarModuleShiftOppImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (op (shiftModule s M))) (F.obj (op M)) (-s) :=
  let := φ.toAlgebra
  (F.map (op (shiftModule s M)) (op M)).f (-s)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)

def scalarModuleShiftOppImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (op M)) (F.obj (op (shiftModule s M))) s :=
  let := φ.toAlgebra
  (s * s).negOnePow • (F.map (op M) (op (shiftModule s M))).f s
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)

lemma scalarModuleShiftOppImageOut_d (s : ℤ) (M : RightModule A D) :
    δ (-s) (-s + 1) (scalarModuleShiftOppImageOut φ D F s M) = 0 := by
  let := φ.toAlgebra
  have h := F.map_d_cochain A'
    (x := op (shiftModule s M)) (y := op M)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M) (q := -s + 1)
  have hz : (F.map (op (shiftModule s M)) (op M)).f (-s + 1)
      ((homObject A' (ScalarExtension.DGBaseChange φ (RightModule A D))ᵒᵖ
        (op (shiftModule s M)) (op M)).d (-s) (-s + 1)
        ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)) = 0 := by
    change (F.map (op (shiftModule s M)) (op M)).f (-s + 1)
      ((ModuleCat.extendScalars φ).map ((moduleHom A D M (shiftModule s M)).d (-s) (-s + 1))
        ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)) = 0
    erw [ModuleCat.ExtendScalars.map_tmul φ]
    rw [moduleShiftInElement_d, TensorProduct.tmul_zero, map_zero]
  exact h.symm.trans hz

lemma scalarModuleShiftOppImageOutIn (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftOppImageOut φ D F s M).comp (scalarModuleShiftOppImageIn φ D F s M)
      (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj (op (shiftModule s M)))) := by
  let := φ.toAlgebra
  have hs := opposite_compose A' (ScalarExtension.DGBaseChange φ (RightModule A D))
    (op (shiftModule s M)) (op M) (op (shiftModule s M)) (-s) s 0 (neg_add_cancel s)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := shiftModule s M) (y := M) (z := shiftModule s M)
    (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M) (add_neg_cancel s)
  have he := congrArg (fun z : GradedHom A (shiftModule s M) (shiftModule s M) 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftOutIn A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) (shiftModule s M)
  have hc' := hc.trans (he.trans hu.symm)
  have hs' := hs.trans (congrArg (fun z => (-s * s).negOnePow • z) hc')
  simp only [neg_mul, Int.negOnePow_neg] at hs'
  have h := congrArg (fun z => (F.map (op (shiftModule s M))
    (op (shiftModule s M))).f 0 z) hs'
  rw [DGFunctor.map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change (scalarModuleShiftOppImageOut φ D F s M).comp
      ((F.map (op M) (op (shiftModule s M))).f s
        ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)) (neg_add_cancel s) =
      (s * s).negOnePow • (F.map (op (shiftModule s M)) (op (shiftModule s M))).f 0
        (unitElement A' (op
          (show ScalarExtension.DGBaseChange φ (RightModule A D) from shiftModule s M))).val at h
  rw [F.map_unitElement A', Bimodule.complex_unitElement] at h
  rw [scalarModuleShiftOppImageIn, Cochain.comp_units_smul, h, smul_smul,
    Int.units_mul_self, one_smul]

lemma scalarModuleShiftOppImageInOut (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftOppImageIn φ D F s M).comp (scalarModuleShiftOppImageOut φ D F s M)
      (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (op M))) := by
  let := φ.toAlgebra
  have hs := opposite_compose A' (ScalarExtension.DGBaseChange φ (RightModule A D))
    (op M) (op (shiftModule s M)) (op M) s (-s) 0 (add_neg_cancel s)
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)
    ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := M) (y := shiftModule s M) (z := M)
    (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M) (neg_add_cancel s)
  have he := congrArg (fun z : GradedHom A M M 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftInOut A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) M
  have hc' := hc.trans (he.trans hu.symm)
  have hs' := hs.trans (congrArg (fun z => (s * -s).negOnePow • z) hc')
  simp only [mul_neg, Int.negOnePow_neg] at hs'
  have h := congrArg (fun z => (F.map (op M) (op M)).f 0 z) hs'
  rw [DGFunctor.map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change ((F.map (op M) (op (shiftModule s M))).f s
      ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)).comp
      (scalarModuleShiftOppImageOut φ D F s M) (add_neg_cancel s) =
      (s * s).negOnePow • (F.map (op M) (op M)).f 0
        (unitElement A' (op
          (show ScalarExtension.DGBaseChange φ (RightModule A D) from M))).val at h
  rw [F.map_unitElement A', Bimodule.complex_unitElement] at h
  rw [scalarModuleShiftOppImageIn, Cochain.units_smul_comp, h, smul_smul,
    Int.units_mul_self, one_smul]

def scalarModuleShiftOppImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (op (shiftModule s M)) ≅ (F.obj (op M))⟦-s⟧ :=
  complexShiftIsoOfSumZero A' (scalarModuleShiftOppImageOut φ D F s M)
    (scalarModuleShiftOppImageOut_d φ D F s M) (scalarModuleShiftOppImageIn φ D F s M)
    (neg_add_cancel s) (scalarModuleShiftOppImageOutIn φ D F s M)
    (scalarModuleShiftOppImageInOut φ D F s M)

lemma scalarContraShiftComparison_naturality
    (G : DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D))ᵒᵖ (Complex A'))
    (a : ∀ x, F.obj x ⟶ G.obj x)
    (h : ∀ x y, F.map x y ≫ homPostcompose (F.obj x) (a y) =
      G.map x y ≫ homPrecompose (a x) (G.obj y))
    (s : ℤ) (M : RightModule A D) :
    a (op (shiftModule s M)) ≫ (scalarModuleShiftOppImageIso φ D G s M).hom =
      (scalarModuleShiftOppImageIso φ D F s M).hom ≫
        (CategoryTheory.shiftFunctor (Complex A') (-s)).map (a (op M)) := by
  let := φ.toAlgebra
  change a _ ≫ (complexShiftIsoOfSumZero A' _ _ _ _ _ _).hom =
    (complexShiftIsoOfSumZero A' _ _ _ _ _ _).hom ≫ _
  rw [complexShiftIsoOfSumZero_hom, complexShiftIsoOfSumZero_hom]
  apply HomologicalComplex.hom_ext
  intro i
  rw [comp_f, comp_f, complexShiftComparison_f, complexShiftComparison_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact (closedFamily_action A' a h (op (shiftModule s M)) (op M) (-s) i (i + -s)
    rfl ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M) v).symm

omit F in
lemma scalarModuleHom_shift_square (s : ℤ) (M T : RightModule A D) :
    scalarModuleHom φ D (shiftModule s M) T ≫
      (scalarModuleShiftOppImageIso φ D
        ((scalarModuleDGFunctor φ D).op.comp
          (representable A' (ScalarExtension.rightModule φ D T))) s M).hom =
      (scalarModuleShiftOppImageIso φ D
        (representable A' (show ScalarExtension.DGBaseChange φ (RightModule A D) from T)) s M).hom ≫
          (CategoryTheory.shiftFunctor (Complex A') (-s)).map (scalarModuleHom φ D M T) :=
  scalarContraShiftComparison_naturality φ D
    (representable A' (show ScalarExtension.DGBaseChange φ (RightModule A D) from T))
    ((scalarModuleDGFunctor φ D).op.comp
      (representable A' (ScalarExtension.rightModule φ D T)))
    (fun x => (scalarModuleDGFunctor φ D).map x.unop T)
    (dgHomMap_contra_naturality (scalarModuleDGFunctor φ D) T) s M

omit F in
lemma scalarModuleHom_shift (s : ℤ) (M T : RightModule A D)
    (hM : QuasiIso (scalarModuleHom φ D M T)) :
    QuasiIso (scalarModuleHom φ D (shiftModule s M) T) := by
  have := hM
  have hs : QuasiIso (scalarModuleHom φ D (shiftModule s M) T ≫
      (scalarModuleShiftOppImageIso φ D
        ((scalarModuleDGFunctor φ D).op.comp
          (representable A' (ScalarExtension.rightModule φ D T))) s M).hom) := by
    rw [scalarModuleHom_shift_square φ D s M T]
    infer_instance
  exact quasiIso_of_comp_right (scalarModuleHom φ D (shiftModule s M) T)
    (scalarModuleShiftOppImageIso φ D
      ((scalarModuleDGFunctor φ D).op.comp
        (representable A' (ScalarExtension.rightModule φ D T))) s M).hom

omit F in
instance scalarModuleHomComparisonLocusStableUnderShift :
    (scalarModuleHomComparisonLocus φ D).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨by
    intro X hX
    apply (scalarModuleHomComparisonLocus φ D).prop_of_iso
      (((moduleToHomotopy A D).commShiftIso s).app X.as)
    intro T
    exact scalarModuleHom_shift φ D s X.as (ForgetEnrichment.to (Complex A) T) (hX T)⟩

end SerrePositivity.DifferentialGraded
