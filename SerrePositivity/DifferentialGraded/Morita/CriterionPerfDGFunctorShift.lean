module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfResolvedHomShift

/-! # dg 関手の像における shift の包含と射影の関係 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma criterionPerf_forward_units_smul_right {B : Type w} [DGCategory A B]
    {x y z : B} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (h : p + q = n) (a : ℤˣ) :
    forward A f (a • g) h = a • forward A f g h := by
  simp only [forward, Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

/-- 正規化射影と包含との合成の符号を、元の shift の単位関係から固定する。 -/
lemma criterionPerfShiftIn_normalizedOut (M : RightModule A D) (s : ℤ) :
    forward A (x := M) (y := shiftModule s M) (z := M)
        (moduleShiftInElement A D s M) (normalizedModuleShiftOut A D s M)
        (neg_add_cancel s) =
      (moduleShiftNormalizationExponent s).negOnePow •
        ((-s * s).negOnePow • (unitElement A M).val) := by
  rw [normalizedModuleShiftOut, criterionPerf_forward_units_smul_right,
    forward_eq_signed_compose, moduleShiftInOut]

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))

/-- dg 関手は、正規化射影と包含の同じ全次数関係を保存する。 -/
lemma criterionPerfDGFunctor_shiftInOut (M : RightModule A D) (s : ℤ) :
    forward A (x := F.obj M) (y := F.obj (shiftModule s M)) (z := F.obj M)
      ((F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M))
      ((F.map (shiftModule s M) M).f s (normalizedModuleShiftOut A D s M))
      (neg_add_cancel s) =
    forward A (x := F.obj M) (y := shiftModule s (F.obj M)) (z := F.obj M)
      (moduleShiftInElement A E s (F.obj M)) (normalizedModuleShiftOut A E s (F.obj M))
      (neg_add_cancel s) := by
  rw [← F.map_forward A, criterionPerfShiftIn_normalizedOut,
    criterionPerfShiftIn_normalizedOut]
  simp only [Units.smul_def, map_zsmul, F.map_unitElement A]

/-- 正規化 shift 同型は、dg 関手で写した次数 -s の包含を元の包含へ送る。 -/
lemma criterionPerfDGFunctor_shiftIn_hom (M : RightModule A D) (s : ℤ) :
    forward A (x := F.obj M) (y := F.obj (shiftModule s M))
      (z := shiftModule s (F.obj M))
      ((F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M))
      (endomorphismClosedElement A E (normalizedDGModuleFunctorShiftIso A D E F s M).hom)
      (add_zero (-s)) = moduleShiftInElement A E s (F.obj M) := by
  apply moduleHomElement_ext A E
  intro x
  rw [moduleHomForward_π]
  erw [endomorphismClosedElement_π]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  apply Cochain.ext
  intro i j hij
  have hi : i = j + s := by omega
  subst i
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    normalizedDGModuleFunctorShiftIso_hom_eval_f]
  have hc := congrArg (fun z => (moduleHomπ A E (F.obj M) (F.obj M) x).f 0 z)
    (criterionPerfDGFunctor_shiftInOut A D E F M s)
  rw [moduleHomForward_π, moduleHomForward_π] at hc
  have hc' := congrArg (fun z => (-s * s).negOnePow • z) hc
  simp only [smul_smul, Int.units_mul_self, one_smul] at hc'
  have hv := congrArg (fun c => c.v (j + s) (j + s) (add_zero (j + s))) hc'
  rw [Cochain.comp_v _ _ _ (j + s) j (j + s) (by omega) rfl,
    Cochain.comp_v _ _ _ (j + s) j (j + s) (by omega) rfl,
    normalizedModuleShiftOut_v, Category.comp_id] at hv
  exact hv

/-- 逆 shift 比較による前合成は、dg 関手が写した包含を復元する。 -/
lemma criterionPerfDGFunctor_shiftIn_inv (M : RightModule A D) (s : ℤ) :
    forward A (x := F.obj M) (y := shiftModule s (F.obj M))
      (z := F.obj (shiftModule s M))
      (moduleShiftInElement A E s (F.obj M))
      (endomorphismClosedElement A E (normalizedDGModuleFunctorShiftIso A D E F s M).inv)
      (add_zero (-s)) =
    (F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M) := by
  let e := normalizedDGModuleFunctorShiftIso A D E F s M
  apply moduleHomElement_ext A E
  intro x
  rw [moduleHomForward_π]
  erw [endomorphismClosedElement_π]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  have h := congrArg (fun z => ((moduleHomπ A E (F.obj M)
    (shiftModule s (F.obj M)) x).f (-s) z).v i j hij)
    (criterionPerfDGFunctor_shiftIn_hom A D E F M s)
  rw [moduleHomForward_π] at h
  erw [endomorphismClosedElement_π] at h
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h
  have ht := congrArg (fun k => k ≫ ((moduleEvaluation A E x).map e.inv).f j) h.symm
  rw [Category.assoc, ← comp_f, ← CategoryTheory.Functor.map_comp,
    e.hom_inv_id] at ht
  erw [CategoryTheory.Functor.map_id, id_f, Category.comp_id] at ht
  exact ht

/-- dg 関手の全 Hom 射は、正規化した像の shift と源 shift の chain 比較に両立する。 -/
lemma criterionPerfDGFunctorHom_sourceShift (M N : RightModule A D) (s : ℤ) :
    F.map (shiftModule s M) N ≫
        eHomWhiskerRight (Complex A) (normalizedDGModuleFunctorShiftIso A D E F s M).inv
          (ForgetEnrichment.of (Complex A) (F.obj N)) ≫
        (moduleHomSourceShiftIso A E (F.obj M) (F.obj N) s).hom =
      (moduleHomSourceShiftIso A D M N s).hom ≫
        (CategoryTheory.shiftFunctor (Complex A) (-s)).map (F.map M N) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (moduleHomSourceShiftIso A E (F.obj M) (F.obj N) s).hom.f q
      ((eHomWhiskerRight (Complex A) (normalizedDGModuleFunctorShiftIso A D E F s M).inv
        (ForgetEnrichment.of (Complex A) (F.obj N))).f q ((F.map (shiftModule s M) N).f q z)) =
    (F.map M N).f (q + -s) ((moduleHomSourceShiftIso A D M N s).hom.f q z)
  rw [criterionPerfHomSourceShiftIso_apply, criterionPerfHomSourceShiftIso_apply]
  erw [criterionPerfHomPrecompose_apply]
  rw [← forward_assoc_of_sum A _ _ _ (add_zero (-s)) (zero_add q) (by omega)]
  erw [criterionPerfDGFunctor_shiftIn_inv A D E F M s]
  exact (F.map_forward A _ _ (by omega)).symm

end SerrePositivity.DifferentialGraded.Morita
