module
public import SerrePositivity.DifferentialGraded.Endomorphism.ConeTriangleMapIso
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomotopyShift
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleConeImage
public import SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles

/-! # 実際の係数拡大のcone連結射と三角形の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex Pretriangulated
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleExtensionConeComparison_fst_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : D) (i : ℤ) :
    ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      (scalarModuleExtensionConeComparison φ D f)).f i ≫
        (((mappingCone.fst ((moduleEvaluation A D x).map f)).val.map
          (ModuleCat.extendScalars φ)).v i (i + 1) rfl) =
      (mappingCone.fst ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
        ((ScalarExtension.moduleExtension φ D).map f))).val.v i (i + 1) rfl := by
  rw [scalarModuleExtensionConeComparison, moduleConeDescOfBoundary_eval]
  let L := ModuleCat.extendScalars φ
  let g := (moduleEvaluation A D x).map f
  have hα := scalarModuleHomElement_π_map φ D (moduleConeInlElement A D f) x
  rw [moduleConeInlElement_π] at hα
  have hβ := ScalarExtension.moduleExtension_eval φ D (moduleConeInr A D f) x
  rw [moduleConeInr_eval] at hβ
  apply complexConeDesc_fst A' _ _ _ ((mappingCone.fst g).val.map L)
  · apply (congrArg (fun z => z.comp ((mappingCone.fst g).val.map L) (neg_add_cancel 1)) hα).trans
    simpa only [Cochain.map_comp, Cochain.map_ofHom, CategoryTheory.Functor.map_id] using
      congrArg (fun z => z.map L) (mappingCone.inl_fst g)
  · rw [hβ]
    simpa only [Cochain.map_comp, Cochain.map_ofHom, Cochain.map_zero] using
      congrArg (fun z => z.map L) (mappingCone.inr_fst g)

lemma scalarModuleExtensionConnecting_eval_f {M N : ModuleCategory A D} (f : M ⟶ N)
    (x : D) (i : ℤ) :
    ((moduleEvaluation A' (ScalarExtension.DGBaseChange φ D) x).map
      ((ScalarExtension.moduleExtension φ D).map (moduleConeConnecting A D f) ≫
        (normalizedScalarModuleExtensionShiftIso φ D 1
          (ForgetEnrichment.to (Complex A) M)).hom)).f i =
      -(((mappingCone.fst ((moduleEvaluation A D x).map f)).val.map
        (ModuleCat.extendScalars φ)).v i (i + 1) rfl) := by
  rw [CategoryTheory.Functor.map_comp, comp_f,
    normalizedScalarModuleExtensionShiftIso_hom_eval_f φ D 1
      (ForgetEnrichment.to (Complex A) M) x i]
  have he := ScalarExtension.moduleExtension_eval φ D (moduleConeConnecting A D f) x
  have hs := moduleConeConnecting_eval A D f x
  have h := congrArg (fun k => ((ScalarExtension.extension φ).map k).f i) hs
  apply (congrArg (fun k => k.f i) he).trans
  apply h.trans
  change (ModuleCat.extendScalars φ).map ((mappingCone.triangle
    ((moduleEvaluation A D x).map f)).mor₃.f i) = _
  simp only [SerrePositivity.coneTriangle_mor₃_f, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id, CategoryTheory.Functor.map_neg, Cochain.map_v]

lemma scalarModuleExtensionConeComparison_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    scalarModuleExtensionConeComparison φ D f ≫
        (ScalarExtension.moduleExtension φ D).map (moduleConeConnecting A D f) ≫
          (normalizedScalarModuleExtensionShiftIso φ D 1 (ForgetEnrichment.to (Complex A) M)).hom =
      moduleConeConnecting A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.hom_ext
  intro i
  rw [CategoryTheory.Functor.map_comp, comp_f,
    scalarModuleExtensionConnecting_eval_f φ D f (show D from x) i,
    moduleConeConnecting_eval A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f) x,
    SerrePositivity.coneTriangle_mor₃_f]
  simp only [Preadditive.comp_neg, shiftFunctorObjXIso, XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  exact congrArg Neg.neg (scalarModuleExtensionConeComparison_fst_eval φ D f (show D from x) i)

local instance : (ScalarExtension.moduleExtension φ D).CommShift ℤ :=
  scalarModuleExtensionCommShift φ D

def scalarModuleExtensionConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeTriangle A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) ≅
      (ScalarExtension.moduleExtension φ D).mapTriangle.obj (moduleConeTriangle A D f) :=
  coneTriangleMapIso (ScalarExtension.moduleExtension φ D) f
    (moduleConeInr A D f) (moduleConeConnecting A D f)
    (moduleConeInr A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f))
    (moduleConeConnecting A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f))
    (scalarModuleExtensionConeIso φ D f)
    (scalarModuleExtensionConeComparison_inr φ D f)
    (scalarModuleExtensionConeComparison_connecting φ D f)

local instance : (scalarModuleExtensionHomotopy φ D).CommShift ℤ :=
  scalarModuleExtensionHomotopyCommShift φ D

def scalarModuleExtensionHomotopyConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (scalarModuleExtensionHomotopy φ D).mapTriangle.obj (moduleHomotopyConeTriangle A D f) ≅
      moduleHomotopyConeTriangle A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) := by
  let := scalarModuleExtensionHomotopyFacIso_commShift φ D
  exact mapTriangleSquareIso (moduleToHomotopy A D) (scalarModuleExtensionHomotopy φ D)
    (ScalarExtension.moduleExtension φ D)
    (moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D))
    (scalarModuleExtensionHomotopyFacIso φ D)
    (moduleConeTriangle A D f)
    (moduleConeTriangle A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f))
    (scalarModuleExtensionConeTriangleIso φ D f).symm

lemma scalarModuleExtensionHomotopyIsTriangulated :
    (scalarModuleExtensionHomotopy φ D).IsTriangulated where
  map_distinguished T hT := by
    change T ∈ moduleDistinguishedTriangles A D at hT
    obtain ⟨M, N, f, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _
      (moduleHomotopyConeTriangle_distinguished A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f)) _
      ((scalarModuleExtensionHomotopy φ D).mapTriangle.mapIso e ≪≫
        scalarModuleExtensionHomotopyConeTriangleIso φ D f)

end SerrePositivity.DifferentialGraded
