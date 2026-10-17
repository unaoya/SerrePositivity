module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelDerivedComparison
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionPerfectSquares
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelColumns
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarDerivedProjectiveComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarRepresentable

/-! # 実際のkernel導来係数変更正方形のPerf制限

係数変更後の列のperfect性も元の列と実際の導来正方形から証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 導来係数変更は代表加群を実際の係数変更後の代表加群へ送る。 -/
def scalarDerivedRepresentableIso (d : D) :
    (derivedExtension φ D).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (moduleToDerived A' (DGBaseChange φ D)).obj
        (ForgetEnrichment.of (Complex A') (representable A' (show DGBaseChange φ D from d))) :=
  scalarDerivedProjectiveComputation φ D
      (ForgetEnrichment.of (Complex A) (representable A d))
      (representable_homotopicallyProjective A D d) ≪≫
    (moduleToDerived A' (DGBaseChange φ D)).mapIso
      (eqToIso (congrArg (ForgetEnrichment.of (Complex A')) (scalarRepresentable_eq φ D d)))

variable (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 代表入力での通常kernelの実際の導来作用は右列を計算する。 -/
def scalarKernelRawColumnIso (d : D) :
    (kernelDerivedTensorOnBimodule A D E P).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (moduleToDerived A E).obj (ForgetEnrichment.of (Complex A) (P.rightAt d)) :=
  ((kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)).symm).app _ ≪≫
    kernelDerivedColumnActionIso A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)) d ≪≫
    kernelDerivedColumnComputation A D E d (BimoduleCategory.of A E D P)

lemma scalarKernelDerivedBaseChange_columnsPerfect
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    ∀ d : DGBaseChange φ D, modulePerfect A' (DGBaseChange φ E)
      ((moduleToDerived A' (DGBaseChange φ E)).obj
        (ForgetEnrichment.of (Complex A') ((scalarKernel φ D E P).rightAt d))) := by
  intro d
  let X := (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))
  let e := (scalarKernelDerivedBaseChangeIso φ D E P hAug hP').app X ≪≫
    (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P)).mapIso (scalarDerivedRepresentableIso φ D d) ≪≫
    scalarKernelRawColumnIso (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P) d
  have hX : modulePerfect A D X := modulePerfectOver_representable A D d (Set.mem_univ _)
  exact (modulePerfect A' (DGBaseChange φ E)).prop_of_iso e
    (scalarDerivedExtension_perfect φ E (perfectKernelAction_preserves A D E P hP hX))

/-- 係数変更後の列のperfect性を追加仮定せず、実際の導来比較をPerfへ制限する。 -/
def scalarKernelPerfectDerivedSquare
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    perfectKernelAction A D E P hP ⋙ scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectKernelAction A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)
          (scalarKernelDerivedBaseChange_columnsPerfect φ D E P hP hAug hP') :=
  scalarPerfectSquare φ D E (kernelDerivedTensorOnBimodule A D E P)
    (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P))
    (fun _ h => perfectKernelAction_preserves A D E P hP h)
    (fun _ h => perfectKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P) (scalarKernelDerivedBaseChange_columnsPerfect φ D E P hP hAug hP') h)
    (scalarKernelDerivedBaseChangeIso φ D E P hAug hP')

lemma scalarKernelPerfectDerivedSquare_inclusion
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    Functor.whiskerRight (scalarKernelPerfectDerivedSquare φ D E P hP hAug hP').hom
        (perfectModuleInclusion A' (DGBaseChange φ E) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (scalarKernelDerivedBaseChangeIso φ D E P hAug hP').hom := rfl

/-- 出力の局所Hom条件とhPN・hP'を保持した、実際のPerf係数変更正方形。 -/
def scalarKernelPerfectDerivedSquare_ofKFlatModels
    (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt d))))
    (hE : localHomKFlat A E)
    (hPN : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        (P.leftAt e)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    perfectKernelAction A D E P hP ⋙ scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectKernelAction A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)
          (scalarKernelDerivedBaseChange_columnsPerfect φ D E P hP
            (scalarKernelOutputAugmentation_isIso φ D E P hE hPN) hP') :=
  scalarKernelPerfectDerivedSquare φ D E P hP
    (scalarKernelOutputAugmentation_isIso φ D E P hE hPN) hP'

end SerrePositivity.DifferentialGraded.Morita
