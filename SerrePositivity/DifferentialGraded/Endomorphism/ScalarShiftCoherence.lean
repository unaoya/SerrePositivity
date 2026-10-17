module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomElementComponents
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarProjectiveImage
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftAddCoherence

/-! # 実際の加群係数拡大の正規化されたshift比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedScalarModuleShift_naturality (s : ℤ) (M : RightModule A D) :
    ∀ x y, (ScalarExtension.rightModule φ D (shiftModule s M)).map x y ≫
        homPostcompose ((ScalarExtension.rightModule φ D (shiftModule s M)).obj x)
          (((ScalarExtension.extension φ).commShiftIso s).app (M.obj y)).hom =
      (shiftModule s (ScalarExtension.rightModule φ D M)).map x y ≫
        homPrecompose (((ScalarExtension.extension φ).commShiftIso s).app (M.obj x)).hom
          ((shiftModule s (ScalarExtension.rightModule φ D M)).obj y) := by
  apply moduleShiftRepresentation_naturality A' (ScalarExtension.DGBaseChange φ D) s
    (scalarModuleHomElement φ D (normalizedModuleShiftOut A D s M))
  intro x i
  have h := congrArg (fun z => z.v i (i + s) rfl)
    (scalarModuleHomElement_π_map φ D (normalizedModuleShiftOut A D s M) x.unop)
  simp only [Cochain.map_v, normalizedModuleShiftOut_v, CategoryTheory.Functor.map_id] at h
  change 𝟙 _ = _
  exact h.symm

/-- 評価成分が通常の複体系数変更のshift比較となる正規化同型。 -/
def normalizedScalarModuleExtensionShiftIso (s : ℤ) (M : RightModule A D) :
    (ScalarExtension.moduleExtension φ D).obj
        (ForgetEnrichment.of (Complex A) (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex A') (shiftModule s (ScalarExtension.rightModule φ D M)) :=
  moduleIsoMk A' (ScalarExtension.DGBaseChange φ D)
    (fun x => ((ScalarExtension.extension φ).commShiftIso s).app (M.obj x))
    (normalizedScalarModuleShift_naturality φ D s M)

lemma normalizedScalarModuleExtensionShiftIso_hom_eval_f (s : ℤ) (M : RightModule A D)
    (x : ScalarExtension.DGBaseChange φ D) (i : ℤ) :
    ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      (normalizedScalarModuleExtensionShiftIso φ D s M).hom).f i = 𝟙 _ := by
  rw [normalizedScalarModuleExtensionShiftIso, moduleIsoMk_hom_eval]
  rfl

lemma normalizedScalarModuleExtensionShiftIso_naturality (s : ℤ)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (ScalarExtension.moduleExtension φ D).map ((moduleShiftFunctor A D s).map f) ≫
        (normalizedScalarModuleExtensionShiftIso φ D s (ForgetEnrichment.to (Complex A) N)).hom =
      (normalizedScalarModuleExtensionShiftIso φ D s (ForgetEnrichment.to (Complex A) M)).hom ≫
        (moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) s).map
          ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, comp_f, comp_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f,
    ScalarExtension.moduleExtension_eval]
  have hs := congrArg (fun k => ((ScalarExtension.extension φ).map k).f i)
    (moduleShiftFunctor_map_eval A D s f (show D from x))
  have ht := congrArg (fun k => k.f i)
    (moduleShiftFunctor_map_eval A' (ScalarExtension.DGBaseChange φ D) s
      ((ScalarExtension.moduleExtension φ D).map f) x)
  have he := congrArg (fun k => k.f (i + s)) (ScalarExtension.moduleExtension_eval φ D f x)
  exact hs.trans (he.symm.trans ht.symm)

def normalizedScalarModuleExtensionShiftNatIso (s : ℤ) :
    moduleShiftFunctor A D s ⋙ ScalarExtension.moduleExtension φ D ≅
      ScalarExtension.moduleExtension φ D ⋙
        moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) s :=
  NatIso.ofComponents
    (F := moduleShiftFunctor A D s ⋙ ScalarExtension.moduleExtension φ D)
    (G := ScalarExtension.moduleExtension φ D ⋙
      moduleShiftFunctor A' (ScalarExtension.DGBaseChange φ D) s)
    (fun M => normalizedScalarModuleExtensionShiftIso φ D s (ForgetEnrichment.to (Complex A) M))
    (fun {M N} f =>
      normalizedScalarModuleExtensionShiftIso_naturality φ D s (M := M) (N := N) f)

def normalizedScalarModuleExtensionCommShiftIso (s : ℤ) :
    CategoryTheory.shiftFunctor (ModuleCategory A D) s ⋙ ScalarExtension.moduleExtension φ D ≅
      ScalarExtension.moduleExtension φ D ⋙
        CategoryTheory.shiftFunctor (ModuleCategory A' (ScalarExtension.DGBaseChange φ D)) s := by
  rw [moduleShiftFunctor_eq, moduleShiftFunctor_eq]
  exact normalizedScalarModuleExtensionShiftNatIso φ D s

lemma normalizedScalarModuleExtensionShiftNatIso_zero :
    normalizedScalarModuleExtensionShiftNatIso φ D 0 =
      CategoryTheory.Functor.CommShift.isoZero (ScalarExtension.moduleExtension φ D) ℤ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  change ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
    (normalizedScalarModuleExtensionShiftIso φ D 0 (ForgetEnrichment.to (Complex A) M)).hom).f i = _
  rw [normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D 0
    (ForgetEnrichment.to (Complex A) M) x i]
  simp only [CategoryTheory.Functor.CommShift.isoZero_hom_app,
    CategoryTheory.Functor.map_comp, comp_f, moduleShiftZero_eq A D,
    moduleShiftZero_eq A' (ScalarExtension.DGBaseChange φ D)]
  rw [ScalarExtension.moduleExtension_eval φ D ((moduleShiftZeroIso A D).hom.app M) x,
    moduleShiftZeroIso_hom_eval A D M (show D from x),
    moduleShiftZeroIso_inv_eval A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).obj M) x]
  have h := congrArg (fun e => (e.hom.app
    ((moduleEvaluation A D (show D from x)).obj M)).f i)
    ((ScalarExtension.extension φ).commShiftIso_zero ℤ)
  simp only [CategoryTheory.Functor.CommShift.isoZero_hom_app, comp_f] at h
  exact h

lemma normalizedScalarModuleExtensionCommShiftIso_zero :
    normalizedScalarModuleExtensionCommShiftIso φ D 0 =
      CategoryTheory.Functor.CommShift.isoZero (ScalarExtension.moduleExtension φ D) ℤ :=
  normalizedScalarModuleExtensionShiftNatIso_zero φ D

end SerrePositivity.DifferentialGraded
