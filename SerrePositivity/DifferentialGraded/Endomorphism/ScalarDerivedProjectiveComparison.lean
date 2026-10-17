module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarPerfectEnhancement
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionNaturality

/-! # 射影的加群での既存導来係数拡大と実際の係数拡大の一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarDerivedExtensionAugmentation_isIso_of_projective (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    IsIso ((ScalarExtension.derivedExtensionAugmentation φ D).app M) := by
  let P := moduleCanonicalProjectiveResolution A D M
  have : IsIso ((moduleToHomotopy A D).map P.π) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D P.projective hM P.π P.quasiIso
  have : IsIso ((moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).map
      ((ScalarExtension.moduleExtension φ D).map P.π)) := by
    change IsIso ((ScalarExtension.moduleExtensionHomotopyToDerived φ D).map
      ((moduleToHomotopy A D).map P.π))
    infer_instance
  rw [ScalarExtension.derivedExtensionAugmentation_app]
  infer_instance

def scalarDerivedProjectiveComputation (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    (ScalarExtension.derivedExtension φ D).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).obj
        ((ScalarExtension.moduleExtension φ D).obj M) := by
  have := scalarDerivedExtensionAugmentation_isIso_of_projective φ D M hM
  exact asIso ((ScalarExtension.derivedExtensionAugmentation φ D).app M)

lemma scalarDerivedProjectiveComputation_naturality {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) :
    (ScalarExtension.derivedExtension φ D).map ((moduleToDerived A D).map f) ≫
        (scalarDerivedProjectiveComputation φ D N hN).hom =
      (scalarDerivedProjectiveComputation φ D M hM).hom ≫
        (moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).map
          ((ScalarExtension.moduleExtension φ D).map f) :=
  (ScalarExtension.derivedExtensionAugmentation φ D).naturality f

end SerrePositivity.DifferentialGraded
