module
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluation
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor
public import SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor

/-! # kernel作用評価とU12d導来tensorの比較のkernel射自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]

lemma kernelHomotopyEvaluationIso_app (P : Bimodule A E D) (e : E)
    (M : ModuleCategory A D) :
    (perfectKernelTensorHomotopyEvaluationIso A D E P e).hom.app
        ((moduleToHomotopy A D).obj M) =
      (moduleDerivedEvaluationHomotopyFacIso A E e).hom.app
          ((kernelTensor A D E P).onClosed.obj M) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app
          ((BalancedTensor.rightTensorFunctor A D (P.leftAt e)).obj M) := by
  simp only [perfectKernelTensorHomotopyEvaluationIso, Quotient.natIsoLift_hom,
    Quotient.natTransLift_app, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    perfectKernelTensorHomotopyEvaluationFacIso, perfectKernelU12dHomotopyTensorFacIso,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    eqToIso.hom, eqToIso.inv, eqToHom_app, perfectKernelTensorEvaluationIso,
    NatIso.ofComponents, Iso.refl_hom]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

lemma kernelHomotopyEvaluationIso_naturality
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') (e : E) :
    Functor.whiskerRight
        (Functor.whiskerRight (kernelTensorHomotopyMap A D E f)
          (moduleHomotopyToDerivedClosed A E)) (moduleDerivedEvaluation A E e) ≫
        (perfectKernelTensorHomotopyEvaluationIso A D E
          (BimoduleCategory.underlying A E D P') e).hom =
      (perfectKernelTensorHomotopyEvaluationIso A D E
        (BimoduleCategory.underlying A E D P) e).hom ≫
        Functor.whiskerRight (BalancedTensor.rightTensorHomotopyLeftMap A D
          ((BimoduleCategory.leftEvaluation A E D e).map f)) DerivedCategory.Qh := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (moduleDerivedEvaluation A E e).map ((moduleHomotopyToDerivedClosed A E).map
      ((kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M))) ≫
      (perfectKernelTensorHomotopyEvaluationIso A D E
        (BimoduleCategory.underlying A E D P') e).hom.app ((moduleToHomotopy A D).obj M) =
    (perfectKernelTensorHomotopyEvaluationIso A D E
      (BimoduleCategory.underlying A E D P) e).hom.app ((moduleToHomotopy A D).obj M) ≫
      DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyLeftMap A D
        ((BimoduleCategory.leftEvaluation A E D e).map f)).app ((moduleToHomotopy A D).obj M))
  rw [kernelTensorHomotopyMap_app, kernelHomotopyEvaluationIso_app,
    kernelHomotopyEvaluationIso_app, BalancedTensor.rightTensorHomotopyLeftMap_app]
  have h := (moduleDerivedEvaluationHomotopyFacIso A E e).hom.naturality
    ((kernelTensorMap A D E f).app M)
  simp only [Functor.comp_map] at h
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc]
  dsimp only [moduleEvaluationToDerived, Functor.comp_map]
  erw [kernelTensorMap_value, DerivedCategory.quotientCompQhIso_inv_naturality]
  exact (Category.assoc _ _ _).symm

lemma kernelResolutionEvaluationIso_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') (e : E) :
    Functor.whiskerRight (kernelResolutionDerivedTensorMap A D E R f)
        (moduleDerivedEvaluation A E e) ≫
        (perfectKernelResolutionDerivedTensorEvaluationIso A D E
          (BimoduleCategory.underlying A E D P') R e).hom =
      (perfectKernelResolutionDerivedTensorEvaluationIso A D E
        (BimoduleCategory.underlying A E D P) R e).hom ≫
        (moduleResolutionDerivedTensorLeftFunctor A D R).map
          ((BimoduleCategory.leftEvaluation A E D e).map f) := by
  apply NatTrans.ext
  funext X
  have h := NatTrans.congr_app (kernelHomotopyEvaluationIso_naturality A D E f e)
    ((moduleDerivedResolutionFunctor A D R).obj X)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    perfectKernelResolutionDerivedTensorEvaluationIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_hom_app]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  exact h

lemma kernelDerivedEvaluationIso_naturality
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') (e : E) :
    Functor.whiskerRight ((kernelDerivedTensorOnBimoduleFunctor A D E).map f)
        (moduleDerivedEvaluation A E e) ≫
        (perfectKernelDerivedTensorEvaluationIso A D E
          (BimoduleCategory.underlying A E D P') e).hom =
      (perfectKernelDerivedTensorEvaluationIso A D E
        (BimoduleCategory.underlying A E D P) e).hom ≫
        (moduleDerivedTensorLeftFunctor A D).map
          ((BimoduleCategory.leftEvaluation A E D e).map f) :=
  kernelResolutionEvaluationIso_naturality A D E (moduleCanonicalProjectiveResolution A D) f e

/-- 実際のkernel作用の評価を、kernel変数に関する関手として読む。 -/
def kernelDerivedEvaluationFunctor (e : E) :
    BimoduleCategory A E D ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  kernelDerivedTensorOnBimoduleFunctor A D E ⋙
    (Functor.whiskeringRight (DerivedModuleCategory A D) (DerivedModuleCategory A E)
      (DerivedCategory (ModuleCat.{u} A))).obj (moduleDerivedEvaluation A E e)

/-- 既存評価比較はkernel変数と導来入力の両方に自然な関手自然同型。 -/
def kernelDerivedEvaluationIso (e : E) :
    kernelDerivedEvaluationFunctor A D E e ≅
      BimoduleCategory.leftEvaluation A E D e ⋙ moduleDerivedTensorLeftFunctor A D :=
  NatIso.ofComponents
    (fun P => perfectKernelDerivedTensorEvaluationIso A D E
      (BimoduleCategory.underlying A E D P) e)
    (by intro P P' f; exact kernelDerivedEvaluationIso_naturality A D E f e)

end SerrePositivity.DifferentialGraded.Morita
