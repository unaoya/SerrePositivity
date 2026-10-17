module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelDerivedNaturality
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelPerfectSquare

/-! # 実際のPerf係数変更正方形のkernel射自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  {P Q : BimoduleCategory A E D} (f : P ⟶ Q)
  (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D P).rightAt d))))
  (hQ : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D Q).rightAt d))))

/-- 列がperfectな通常kernel間の射を、実際のPerf作用の射へ制限する。 -/
def perfectKernelBimoduleMap :
    perfectKernelAction A D E (BimoduleCategory.underlying A E D P) hP ⟶
      perfectKernelAction A D E (BimoduleCategory.underlying A E D Q) hQ :=
  perfectFunctorTransformation A D E _ _
    (fun _ h => perfectKernelAction_preserves A D E (BimoduleCategory.underlying A E D P) hP h)
    (fun _ h => perfectKernelAction_preserves A D E (BimoduleCategory.underlying A E D Q) hQ h)
    ((kernelDerivedTensorOnBimoduleFunctor A D E).map f)

lemma perfectKernelBimoduleMap_inclusion :
    Functor.whiskerRight (perfectKernelBimoduleMap D E f hP hQ)
        (perfectModuleInclusion A E Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        ((kernelDerivedTensorOnBimoduleFunctor A D E).map f) := rfl

variable
  (hAugP : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hAugQ : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D Q)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hP' : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj)))

/-- Perf正方形の比較射は、モデル条件を満たすkernelの全閉零射に自然。 -/
lemma scalarKernelPerfectDerivedSquare_kernel_naturality :
    Functor.whiskerRight (perfectKernelBimoduleMap D E f hP hQ)
        (scalarExtensionPerfectFunctor φ E Set.univ) ≫
        (scalarKernelPerfectDerivedSquare φ D E (BimoduleCategory.underlying A E D Q)
          hQ hAugQ hP').hom =
      (scalarKernelPerfectDerivedSquare φ D E (BimoduleCategory.underlying A E D P)
        hP hAugP hP').hom ≫
        Functor.whiskerLeft (scalarExtensionPerfectFunctor φ D Set.univ)
          (perfectKernelBimoduleMap (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D P) hP hAugP hP')
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D Q) hQ hAugQ hP')) :=
  scalarPerfectSquare_naturality φ D E _ _ _ _ _ _ _ _ _ _ _ _
    (scalarKernelDerivedBaseChangeIso_kernel_naturality φ D E f hAugP hAugQ hP')

/-- hPN・hP'を保持した実際のPerf正方形もkernel射に自然。 -/
lemma scalarKernelPerfectDerivedSquare_ofKFlatModels_kernel_naturality
    (hE : localHomKFlat A E)
    (hPNP : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        ((BimoduleCategory.underlying A E D P).leftAt e)))
    (hPNQ : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        ((BimoduleCategory.underlying A E D Q).leftAt e))) :
    Functor.whiskerRight (perfectKernelBimoduleMap D E f hP hQ)
        (scalarExtensionPerfectFunctor φ E Set.univ) ≫
        (scalarKernelPerfectDerivedSquare_ofKFlatModels φ D E
          (BimoduleCategory.underlying A E D Q) hQ hE hPNQ hP').hom =
      (scalarKernelPerfectDerivedSquare_ofKFlatModels φ D E
        (BimoduleCategory.underlying A E D P) hP hE hPNP hP').hom ≫
        Functor.whiskerLeft (scalarExtensionPerfectFunctor φ D Set.univ)
          (perfectKernelBimoduleMap (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D P) hP
              (scalarKernelOutputAugmentation_isIso φ D E
                (BimoduleCategory.underlying A E D P) hE hPNP) hP')
            (scalarKernelDerivedBaseChange_columnsPerfect φ D E
              (BimoduleCategory.underlying A E D Q) hQ
              (scalarKernelOutputAugmentation_isIso φ D E
                (BimoduleCategory.underlying A E D Q) hE hPNQ) hP')) :=
  scalarKernelPerfectDerivedSquare_kernel_naturality φ D E f hP hQ
    (scalarKernelOutputAugmentation_isIso φ D E (BimoduleCategory.underlying A E D P) hE hPNP)
    (scalarKernelOutputAugmentation_isIso φ D E (BimoduleCategory.underlying A E D Q) hE hPNQ) hP'

end SerrePositivity.DifferentialGraded.Morita
