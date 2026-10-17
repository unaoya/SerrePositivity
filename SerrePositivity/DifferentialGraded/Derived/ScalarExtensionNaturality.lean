module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionComplex

/-! # 導来係数拡大の underived 比較の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 解像度族の増大射は、係数変更後の導来圏で自然。 -/
def resolutionExtensionAugmentation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⋙ moduleExtensionHomotopyToDerived φ D ⟶
      moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D) where
  app M := (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map (R M).π)
  naturality {M N} f := by
    have h := congrArg (moduleExtensionHomotopyToDerived φ D).map ((R M).lift_fac (R N) f)
    simp only [CategoryTheory.Functor.map_comp] at h
    convert h using 1 <;> rfl

/-- 主導来関手から underived 係数拡大への自然な比較。
成分が同型かどうかは K-flat 条件によって別に判定する。 -/
def derivedExtensionAugmentation :
    moduleToDerived A D ⋙ derivedExtension φ D ⟶
      moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D) :=
  Functor.whiskerRight (moduleDerivedResolutionFunctor_fac A D
    (moduleCanonicalProjectiveResolution A D)).hom (moduleExtensionHomotopyToDerived φ D) ≫
      resolutionExtensionAugmentation φ D (moduleCanonicalProjectiveResolution A D)

lemma derivedExtensionAugmentation_app (M : ModuleCategory A D) :
    (derivedExtensionAugmentation φ D).app M =
      (resolutionDerivedExtensionComputation φ D (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (moduleToDerived A' (DGBaseChange φ D)).map
          ((moduleExtension φ D).map (moduleCanonicalProjectiveResolution A D M).π) := rfl

lemma derivedExtensionAugmentation_isIso_of_objectwiseKFlat (M : ModuleCategory A D)
    (hD : localHomKFlat A D)
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso ((derivedExtensionAugmentation φ D).app M) := by
  have hP := moduleSemifree_objectwiseKFlat A D hD
    (moduleResolutionCandidate_semifree A D M)
  have hπ := moduleExtension_quasiIso_of_objectwiseKFlat φ D hP hM
    (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso
  have := moduleToDerived_inverts A' (DGBaseChange φ D) _ hπ
  rw [derivedExtensionAugmentation_app]
  infer_instance

end SerrePositivity.DifferentialGraded.ScalarExtension
