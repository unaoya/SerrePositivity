module
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensor
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelEvaluation
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelOutputModels

/-! # kernel評価比較の標準解像度成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]

lemma scalarKernelEvaluationHomotopy_closed (e : E) (M : ModuleCategory A D) :
    (perfectKernelTensorHomotopyEvaluationIso A D E P e).hom.app
        ((moduleToHomotopy A D).obj M) ≫
        (perfectKernelU12dHomotopyTensorFacIso A D E P e).hom.app M =
      (perfectKernelTensorHomotopyEvaluationFacIso A D E P e).hom.app M := by
  simp only [perfectKernelTensorHomotopyEvaluationIso, Quotient.natIsoLift_hom,
    Quotient.natTransLift_app, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc]
  change _ ≫ ((perfectKernelU12dHomotopyTensorFacIso A D E P e).app M).inv ≫
    ((perfectKernelU12dHomotopyTensorFacIso A D E P e).app M).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

lemma scalarKernelEvaluationClosed_fac (e : E) (M : ModuleCategory A D) :
    (perfectKernelTensorHomotopyEvaluationFacIso A D E P e).hom.app M =
      (moduleDerivedEvaluation A E e).map (kernelTensorHomotopyComputation A D E P M).hom ≫
        (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
          ((kernelTensor A D E P).onClosed.obj M) := by
  simp only [perfectKernelTensorHomotopyEvaluationFacIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    moduleDerivedEvaluationHomotopyFacIso, perfectKernelTensorEvaluationIso,
    NatIso.ofComponents, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp, eqToIso.hom]
  rw [scalarKernelOutputHomotopyComputation_hom]
  simp only [eqToHom_refl, eqToHom_app, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]

lemma scalarKernelU12dClosed_fac (e : E) (M : ModuleCategory A D) :
    (perfectKernelU12dHomotopyTensorFacIso A D E P e).hom.app M =
      DerivedCategory.Qh.map (moduleTensorHomotopyComputation A D (P.leftAt e) M).hom ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app
          ((BalancedTensor.rightTensorFunctor A D (P.leftAt e)).obj M) := by
  simp only [perfectKernelU12dHomotopyTensorFacIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    eqToIso.hom, eqToHom_app]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  change 𝟙 _ ≫ _ = DerivedCategory.Qh.map (𝟙 _) ≫ _
  rw [CategoryTheory.Functor.map_id]

/-- U12d評価比較とkernel計算の標準解像度成分は一致する。 -/
lemma scalarKernelResolutionEvaluation_computation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (e : E) (M : ModuleCategory A D) :
    (moduleDerivedEvaluation A E e).map
        (kernelResolutionDerivedTensorComputation A D E P R M).hom ≫
        (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
          ((kernelTensor A D E P).onClosed.obj (R M).obj) =
      (perfectKernelResolutionDerivedTensorEvaluationIso A D E P R e).hom.app
          ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorComputation A D R (P.leftAt e) M).hom := by
  have hn := (perfectKernelTensorHomotopyEvaluationIso A D E P e).hom.naturality
    (moduleDerivedResolutionComputation A D R M).hom
  simp only [Functor.comp_map] at hn
  simp only [perfectKernelResolutionDerivedTensorEvaluationIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  erw [Category.id_comp]
  simp only [moduleResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map]
  rw [← Category.assoc]
  erw [← hn]
  simp only [Category.assoc]
  erw [← scalarKernelU12dClosed_fac, scalarKernelEvaluationHomotopy_closed,
    scalarKernelEvaluationClosed_fac]
  simp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- 相対K-flat入力でのU12d計算と、実際のkernel増大の評価は一致する。 -/
lemma scalarKernelEvaluationAugmentation_relativeKFlat (e : E) (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (moduleDerivedEvaluation A E e).map ((kernelDerivedTensorAugmentation A D E P).app M) ≫
        (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.app
          ((kernelTensor A D E P).onClosed.obj M) =
      (perfectKernelDerivedTensorEvaluationIso A D E P e).hom.app ((moduleToDerived A D).obj M) ≫
        (ScalarExtension.relativeKFlatTensorComputation D M hM (P.leftAt e)).hom := by
  rw [kernelDerivedTensorAugmentation_app, CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (eqToIso (moduleDerivedEvaluation_fac A E e)).hom.naturality
    ((kernelTensor A D E P).onClosed.map (moduleCanonicalProjectiveResolution A D M).π)
  simp only [Functor.comp_map] at hn
  erw [hn]
  rw [← Category.assoc, scalarKernelResolutionEvaluation_computation]
  simp only [ScalarExtension.relativeKFlatTensorComputation, Iso.trans_hom, asIso_hom,
    Category.assoc]
  simp only [moduleEvaluationToDerived, Functor.comp_map]
  rw [perfectKernelTensor_map_eval]
  rfl

end SerrePositivity.DifferentialGraded.Morita
