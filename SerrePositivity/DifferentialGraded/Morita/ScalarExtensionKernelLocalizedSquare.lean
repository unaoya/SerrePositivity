module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizationAugmentation
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelPerfectSquare

/-! # 局所化したkernel係数変更への実際の作用正方形

通常モデルへの増大の可逆性を明示し、既存のdg加群値の比較を主kernelの
係数変更関手へ接続する。増大の可逆性をhPN・hP'から推論しない。
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
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : BimoduleCategory A E D)
  (hα : IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P))

/-- 主kernel係数変更の作用を、増大で通常係数変更モデルの作用へ比較する。 -/
def scalarKernelLocalizedActionIso :
    kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
        ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) ≅
      kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E (BimoduleCategory.underlying A E D P)) := by
  let := hα
  exact (kernelDerivedTensorFunctor A' (DGBaseChange φ D) (DGBaseChange φ E)).mapIso
      (asIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P)) ≪≫
    kernelDerivedTensorOnBimoduleIso A' (DGBaseChange φ D) (DGBaseChange φ E)
      ((scalarKernelFunctor φ D E).obj P)

variable
  (hAug : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hP' : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj)))

/-- 通常モデルの正方形を、実際の主局所化kernel係数変更の作用へ接続する。 -/
def scalarKernelLocalizedDerivedSquare :
    kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P) ⋙ derivedExtension φ E ≅
      derivedExtension φ D ⋙
        kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) :=
  Functor.isoWhiskerRight (kernelDerivedTensorOnBimoduleIso A D E P) _ ≪≫
    scalarKernelDerivedBaseChangeIso φ D E (BimoduleCategory.underlying A E D P) hAug hP' ≪≫
    Functor.isoWhiskerLeft (derivedExtension φ D) (scalarKernelLocalizedActionIso φ D E P hα).symm

/-- 増大後の局所化正方形は、既存の通常モデルの比較そのものである。 -/
lemma scalarKernelLocalizedDerivedSquare_augmentation :
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP').hom ≫
        Functor.whiskerLeft (derivedExtension φ D) (scalarKernelLocalizedActionIso φ D E P hα).hom =
      Functor.whiskerRight (kernelDerivedTensorOnBimoduleIso A D E P).hom (derivedExtension φ E) ≫
        (scalarKernelDerivedBaseChangeIso φ D E
          (BimoduleCategory.underlying A E D P) hAug hP').hom := by
  simp only [scalarKernelLocalizedDerivedSquare, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Category.assoc]
  rw [← Functor.whiskerLeft_comp, Iso.inv_hom_id]
  simp only [Functor.whiskerLeft_id', Category.comp_id]

include hα hAug hP' in
/-- 元の列がperfectなら、局所化した係数変更kernelも列がperfectである。 -/
lemma scalarKernelLocalized_columnsPerfect
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P)) :
    kernelColumnsPerfect A' (DGBaseChange φ D) (DGBaseChange φ E)
      ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A' (DGBaseChange φ D) (DGBaseChange φ E) _).2
  have hraw := (kernelColumnsPerfect_ofBimodule_iff A D E P).1 hP
  have hscalar := scalarKernelDerivedBaseChange_columnsPerfect φ D E
    (BimoduleCategory.underlying A E D P) hraw hAug hP'
  intro X hX
  exact (modulePerfect A' (DGBaseChange φ E)).prop_of_iso
    ((scalarKernelLocalizedActionIso φ D E P hα).app X).symm
    (perfectKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E (BimoduleCategory.underlying A E D P)) hscalar hX)

/-- 局所化したkernel係数変更への正方形を、両側の実際のPerf作用へ制限する。 -/
def scalarKernelLocalizedPerfectSquare
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P)) :
    perfectDerivedKernelAction A D E ((bimoduleToDerived A E D).obj P) hP ⋙
        scalarExtensionPerfectFunctor φ E Set.univ ≅
      scalarExtensionPerfectFunctor φ D Set.univ ⋙
        perfectDerivedKernelAction A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
          (scalarKernelLocalized_columnsPerfect φ D E P hα hAug hP' hP) :=
  scalarPerfectSquare φ D E _ _
    (fun _ h => perfectDerivedKernelAction_preserves A D E _ hP h)
    (fun _ h => perfectDerivedKernelAction_preserves A' (DGBaseChange φ D) (DGBaseChange φ E) _
      (scalarKernelLocalized_columnsPerfect φ D E P hα hAug hP' hP) h)
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP')

lemma scalarKernelLocalizedPerfectSquare_inclusion
    (hP : kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P)) :
    Functor.whiskerRight (scalarKernelLocalizedPerfectSquare φ D E P hα hAug hP' hP).hom
        (perfectModuleInclusion A' (DGBaseChange φ E) Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP').hom := rfl

end SerrePositivity.DifferentialGraded.Morita
