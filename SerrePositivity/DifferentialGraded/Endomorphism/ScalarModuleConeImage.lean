module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomElementComponents
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarGradedSplit
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleConeImage

/-! # 実際の加群係数拡大と標準coneの比較同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarModuleConeInl {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) M))
      (ScalarExtension.rightModule φ D
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).X (-1) :=
  scalarModuleHomElement φ D (moduleConeInlElement A D f)

lemma scalarModuleConeInl_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) M))
      (ScalarExtension.rightModule φ D
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
      (scalarModuleConeInl φ D f) =
    endomorphismClosedElement A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f ≫
        (ScalarExtension.moduleExtension φ D).map (moduleConeInr A D f)) := by
  rw [scalarModuleConeInl, scalarModuleHomElement_d, moduleConeInlElement_d]
  have h := scalarModuleHomElement_closed φ D (f ≫ moduleConeInr A D f)
  rw [CategoryTheory.Functor.map_comp] at h
  exact h

def scalarModuleExtensionConeComparison {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A' (ScalarExtension.DGBaseChange φ D) ((ScalarExtension.moduleExtension φ D).map f) ⟶
      (ScalarExtension.moduleExtension φ D).obj (moduleCone A D f) :=
  moduleConeDescOfBoundary A' (ScalarExtension.DGBaseChange φ D)
    ((ScalarExtension.moduleExtension φ D).map f) (scalarModuleConeInl φ D f)
    ((ScalarExtension.moduleExtension φ D).map (moduleConeInr A D f))
    (scalarModuleConeInl_d φ D f)

instance scalarModuleExtensionConeComparison_isIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso (scalarModuleExtensionConeComparison φ D f) := by
  apply moduleIsIso_of_evaluations A' (ScalarExtension.DGBaseChange φ D)
  intro x
  rw [scalarModuleExtensionConeComparison, moduleConeDescOfBoundary_eval]
  let L := ModuleCat.extendScalars φ
  let g := (moduleEvaluation A D (show D from x)).map f
  have hα := scalarModuleHomElement_π_map φ D (moduleConeInlElement A D f) (show D from x)
  rw [moduleConeInlElement_π] at hα
  have hβ := ScalarExtension.moduleExtension_eval φ D (moduleConeInr A D f) x
  rw [moduleConeInr_eval] at hβ
  apply complexConeDesc_isIso A' _ _ _ ((mappingCone.fst g).val.map L) ((mappingCone.snd g).map L)
  · apply (congrArg (fun z => z.comp ((mappingCone.fst g).val.map L) (neg_add_cancel 1)) hα).trans
    simpa only [Cochain.map_comp, Cochain.map_ofHom, CategoryTheory.Functor.map_id] using
      congrArg (fun z => z.map L) (mappingCone.inl_fst g)
  · apply (congrArg (fun z => z.comp ((mappingCone.snd g).map L) (add_zero (-1))) hα).trans
    simpa only [Cochain.map_comp, Cochain.map_zero] using
      congrArg (fun z => z.map L) (mappingCone.inl_snd g)
  · rw [hβ]
    simpa only [Cochain.map_comp, Cochain.map_ofHom, Cochain.map_zero] using
      congrArg (fun z => z.map L) (mappingCone.inr_fst g)
  · rw [hβ]
    simpa only [Cochain.map_comp, Cochain.map_ofHom, CategoryTheory.Functor.map_id] using
      congrArg (fun z => z.map L) (mappingCone.inr_snd g)
  · let X' := (ScalarExtension.extension φ).obj ((moduleEvaluation A D (show D from x)).obj M)
    let Y' := (ScalarExtension.extension φ).obj ((moduleEvaluation A D (show D from x)).obj N)
    let K' := (ScalarExtension.extension φ).obj (mappingCone g)
    apply (congrArg₂ (fun (a : Cochain X' K' (-1)) (b : Y' ⟶ K') =>
      ((mappingCone.fst g).val.map L).comp a (add_neg_cancel 1) +
      ((mappingCone.snd g).map L).comp (Cochain.ofHom b) (add_zero 0)) hα hβ).trans
    simpa only [Cochain.map_add, Cochain.map_comp, Cochain.map_ofHom,
      CategoryTheory.Functor.map_id] using congrArg (fun z => z.map L) (mappingCone.id g)

def scalarModuleExtensionConeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A' (ScalarExtension.DGBaseChange φ D) ((ScalarExtension.moduleExtension φ D).map f) ≅
      (ScalarExtension.moduleExtension φ D).obj (moduleCone A D f) :=
  asIso (scalarModuleExtensionConeComparison φ D f)

@[reassoc] lemma scalarModuleExtensionConeComparison_inr {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A' (ScalarExtension.DGBaseChange φ D)
        ((ScalarExtension.moduleExtension φ D).map f) ≫ scalarModuleExtensionConeComparison φ D f =
      (ScalarExtension.moduleExtension φ D).map (moduleConeInr A D f) :=
  moduleConeDescOfBoundary_inr A' (ScalarExtension.DGBaseChange φ D) _ _ _ _

end SerrePositivity.DifferentialGraded
