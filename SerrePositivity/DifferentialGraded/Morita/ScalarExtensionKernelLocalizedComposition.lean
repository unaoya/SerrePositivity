module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizedSquare
public import SerrePositivity.DifferentialGraded.Morita.PerfectDerivedKernelComposition

/-! # 局所化kernel係数変更の作用正方形と実際のkernel合成

通常代表のモデル条件を保持し、公開kernelCompositionIsoを両側に使う。
係数変更関手が合成kernelを保存する同型の存在は入力にも結論にも含めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 通常モデルから局所化係数変更への作用正方形に必要な三つの条件。 -/
structure ScalarKernelLocalizedConditions (P : BimoduleCategory A E D) : Prop where
  augmentationIsIso : IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P)
  outputAugmentation : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj))
  inputRelativeKFlat : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj))

variable (B : Type z) [DGCategory A B] [Small.{u} B]
  (hD : localHomKFlat A D) (hD' : localHomKFlat A' (DGBaseChange φ D))
  (P : BimoduleCategory A E D) (Q : BimoduleCategory A B E)
  (cP : ScalarKernelLocalizedConditions φ D E P)
  (cQ : ScalarKernelLocalizedConditions φ E B Q)

/-- 実際のkernel合成比較を両側に用いる、二つの係数変更正方形の貼合せ。 -/
def scalarKernelLocalizedCompositionSquare :
    kernelDerivedTensor A D B
        (kernelCompose A D E B hD ((bimoduleToDerived A E D).obj P)
          ((bimoduleToDerived A B E).obj Q)) ⋙ derivedExtension φ B ≅
      derivedExtension φ D ⋙ kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ B)
        (kernelCompose A' (DGBaseChange φ D) (DGBaseChange φ E) (DGBaseChange φ B) hD'
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
          ((scalarKernelDerivedExtension φ E B).obj ((bimoduleToDerived A B E).obj Q))) :=
  Functor.isoWhiskerRight
      (kernelCompositionIso A D E B hD ((bimoduleToDerived A E D).obj P)
        ((bimoduleToDerived A B E).obj Q)).symm (derivedExtension φ B) ≪≫
    scalarDerivedSquareComposition φ D E B _ _ _ _
      (scalarKernelLocalizedDerivedSquare φ D E P cP.augmentationIsIso
        cP.outputAugmentation cP.inputRelativeKFlat)
      (scalarKernelLocalizedDerivedSquare φ E B Q cQ.augmentationIsIso
        cQ.outputAugmentation cQ.inputRelativeKFlat) ≪≫
    Functor.isoWhiskerLeft (derivedExtension φ D)
      (kernelCompositionIso A' (DGBaseChange φ D) (DGBaseChange φ E) (DGBaseChange φ B) hD'
        ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
        ((scalarKernelDerivedExtension φ E B).obj ((bimoduleToDerived A B E).obj Q)))

/-- 実際の合成比較とモデル条件付き正方形の貼合せが可換となる図式。 -/
lemma scalarKernelLocalizedCompositionSquare_diagram :
    Functor.whiskerRight
        (kernelCompositionIso A D E B hD ((bimoduleToDerived A E D).obj P)
          ((bimoduleToDerived A B E).obj Q)).hom (derivedExtension φ B) ≫
        (scalarKernelLocalizedCompositionSquare φ D E B hD hD' P Q cP cQ).hom =
      (scalarDerivedSquareComposition φ D E B _ _ _ _
        (scalarKernelLocalizedDerivedSquare φ D E P cP.augmentationIsIso
          cP.outputAugmentation cP.inputRelativeKFlat)
        (scalarKernelLocalizedDerivedSquare φ E B Q cQ.augmentationIsIso
          cQ.outputAugmentation cQ.inputRelativeKFlat)).hom ≫
        Functor.whiskerLeft (derivedExtension φ D)
          (kernelCompositionIso A' (DGBaseChange φ D) (DGBaseChange φ E) (DGBaseChange φ B) hD'
            ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
            ((scalarKernelDerivedExtension φ E B).obj ((bimoduleToDerived A B E).obj Q))).hom := by
  simp only [scalarKernelLocalizedCompositionSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← Category.assoc, ← Category.assoc, ← Functor.whiskerRight_comp, Iso.hom_inv_id]
  simp only [Functor.whiskerRight_id', Category.id_comp]

/-- 実際の合成kernelの係数変更作用図式を、両側のPerfへ制限する。 -/
def scalarKernelLocalizedCompositionPerfectSquare
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P))
    (hQ : kernelColumnsPerfect A E B ((bimoduleToDerived A B E).obj Q)) :=
  scalarPerfectSquare φ D B _ _
    (fun _ h => perfectDerivedKernelAction_preserves A D B _
      (kernelCompose_columnsPerfect_of_columns A D E B hD _ _ hP hQ) h)
    (fun _ h => perfectDerivedKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ B) _
      (kernelCompose_columnsPerfect_of_columns A' (DGBaseChange φ D) (DGBaseChange φ E)
        (DGBaseChange φ B) hD' _ _
        (scalarKernelLocalized_columnsPerfect φ D E P cP.augmentationIsIso
          cP.outputAugmentation cP.inputRelativeKFlat hP)
        (scalarKernelLocalized_columnsPerfect φ E B Q cQ.augmentationIsIso
          cQ.outputAugmentation cQ.inputRelativeKFlat hQ)) h)
    (scalarKernelLocalizedCompositionSquare φ D E B hD hD' P Q cP cQ)

lemma scalarKernelLocalizedCompositionPerfectSquare_inclusion
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P))
    (hQ : kernelColumnsPerfect A E B ((bimoduleToDerived A B E).obj Q)) :
    Functor.whiskerRight
        (scalarKernelLocalizedCompositionPerfectSquare φ D E B hD hD' P Q cP cQ hP hQ).hom
        (perfectModuleInclusion A' (DGBaseChange φ B) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (scalarKernelLocalizedCompositionSquare φ D E B hD hD' P Q cP cQ).hom := rfl

end SerrePositivity.DifferentialGraded.Morita
