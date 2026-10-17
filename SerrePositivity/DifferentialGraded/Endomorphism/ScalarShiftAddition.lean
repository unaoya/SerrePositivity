module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarShiftCoherence

/-! # 実際の係数拡大の正規化shift比較の加法整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarComplexShiftAdd_hom_f (K : Complex A) (s t i : ℤ) :
    ((ScalarExtension.extension φ).map ((shiftFunctorAdd (Complex A) s t).hom.app K)).f i =
      ((shiftFunctorAdd (Complex A') s t).hom.app ((ScalarExtension.extension φ).obj K)).f i := by
  change (ModuleCat.extendScalars φ).map
    (((shiftFunctorAdd (Complex A) s t).hom.app K).f i) = _
  rw [shiftFunctorAdd_hom_app_f, shiftFunctorAdd_hom_app_f]
  simp only [HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedScalarModuleExtensionShiftIso_add_square (s t : ℤ) (M : RightModule A D) :
    (ScalarExtension.moduleExtension φ D).map (moduleShiftAddIsoObj A D s t M).hom ≫
        (normalizedScalarModuleExtensionShiftIso φ D t (shiftModule s M)).hom ≫
        (moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) t).map
          (normalizedScalarModuleExtensionShiftIso φ D s M).hom =
      (normalizedScalarModuleExtensionShiftIso φ D (s + t) M).hom ≫
        (moduleShiftAddIsoObj A' (ScalarExtension.DGBaseChange φ D) s t
          (ScalarExtension.rightModule φ D M)).hom := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, comp_f, comp_f, comp_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D t (shiftModule s M) x i,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D (s + t) M x i]
  have hm := congrArg (fun k => k.f i)
    (moduleShiftFunctor_map_eval A' (ScalarExtension.DGBaseChange φ D) t
      (normalizedScalarModuleExtensionShiftIso φ D s M).hom x)
  have hm' : ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      ((moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) t).map
        (normalizedScalarModuleExtensionShiftIso φ D s M).hom)).f i = 𝟙 _ :=
    hm.trans (normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D s M x (i + t))
  rw [hm']
  simp only [Category.id_comp]
  have hF := congrArg (fun k => k.f i)
    (ScalarExtension.moduleExtension_eval φ D (moduleShiftAddIsoObj A D s t M).hom x)
  have hs := congrArg (fun k => ((ScalarExtension.extension φ).map k).f i)
    (moduleShiftAddIsoObj_hom_eval A D s t M (show D from x))
  have ht := congrArg (fun k => k.f i)
    (moduleShiftAddIsoObj_hom_eval A' (ScalarExtension.DGBaseChange φ D) s t
      (ScalarExtension.rightModule φ D M) x)
  exact hF.trans (hs.trans ((scalarComplexShiftAdd_hom_f φ (M.obj (op x)) s t i).trans ht.symm))

lemma normalizedScalarModuleExtensionShiftNatIso_add (s t : ℤ) :
    normalizedScalarModuleExtensionShiftNatIso φ D (s + t) =
      CategoryTheory.Functor.CommShift.isoAdd
        (C := ModuleCategory A D) (D := ModuleCategory A' (ScalarExtension.DGBaseChange φ D))
        (A := ℤ) (F := ScalarExtension.moduleExtension φ D) (a := s) (b := t)
        (normalizedScalarModuleExtensionShiftNatIso φ D s)
        (normalizedScalarModuleExtensionShiftNatIso φ D t) := by
  apply shiftComparison_eq_isoAdd_of_square
    (C := ModuleCategory A D) (E := ModuleCategory A' (ScalarExtension.DGBaseChange φ D))
    (ScalarExtension.moduleExtension φ D) s t
    (normalizedScalarModuleExtensionShiftNatIso φ D s)
    (normalizedScalarModuleExtensionShiftNatIso φ D t)
    (normalizedScalarModuleExtensionShiftNatIso φ D (s + t))
  intro M
  simp only [moduleShiftAdd_eq A D, moduleShiftAdd_eq A' (ScalarExtension.DGBaseChange φ D),
    moduleShiftFunctor_eq A D, moduleShiftFunctor_eq A' (ScalarExtension.DGBaseChange φ D),
    normalizedScalarModuleExtensionShiftNatIso]
  exact normalizedScalarModuleExtensionShiftIso_add_square φ D s t
    (ForgetEnrichment.to (Complex A) M)

lemma normalizedScalarModuleExtensionCommShiftIso_add (s t : ℤ) :
    normalizedScalarModuleExtensionCommShiftIso φ D (s + t) =
      CategoryTheory.Functor.CommShift.isoAdd
        (C := ModuleCategory A D) (D := ModuleCategory A' (ScalarExtension.DGBaseChange φ D))
        (A := ℤ) (F := ScalarExtension.moduleExtension φ D) (a := s) (b := t)
        (normalizedScalarModuleExtensionCommShiftIso φ D s)
        (normalizedScalarModuleExtensionCommShiftIso φ D t) :=
  normalizedScalarModuleExtensionShiftNatIso_add φ D s t

/-- 零・加法shiftと整合する、実際の加群係数拡大の比較データ。 -/
@[instance_reducible]
def scalarModuleExtensionCommShift : (ScalarExtension.moduleExtension φ D).CommShift ℤ where
  commShiftIso := normalizedScalarModuleExtensionCommShiftIso φ D
  commShiftIso_zero := normalizedScalarModuleExtensionCommShiftIso_zero φ D
  commShiftIso_add := normalizedScalarModuleExtensionCommShiftIso_add φ D

end SerrePositivity.DifferentialGraded
