module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelMapNaturality
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelHomotopy

/-! # kernel係数変更比較のH⁰におけるkernel射自然性 -/
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

lemma scalarKernelBalancedHomotopyIso_app (P : Bimodule A E D)
    (M : ModuleCategory A D) :
    (scalarKernelBalancedHomotopyIso φ D E P).hom.app ((moduleToHomotopy A D).obj M) =
      (moduleToHomotopy A' (DGBaseChange φ E)).map
        (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom := by
  simp only [scalarKernelBalancedHomotopyIso, Quotient.natIsoLift_hom,
    Quotient.natTransLift_app, scalarKernelBalancedHomotopyFacIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    scalarKernelBalancedNatIso, NatIso.ofComponents]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]

lemma scalarKernelExtensionHomotopy_map_closed {M N : ModuleCategory A D} (g : M ⟶ N) :
    (scalarModuleExtensionHomotopy φ D).map ((moduleToHomotopy A D).map g) =
      (moduleToHomotopy A' (DGBaseChange φ D)).map ((moduleExtension φ D).map g) := rfl

lemma scalarKernelBalancedHomotopyIso_kernel_naturality
    {P Q : BimoduleCategory A E D} (f : P ⟶ Q) :
    Functor.whiskerRight (kernelTensorHomotopyMap A D E f)
        (scalarModuleExtensionHomotopy φ E) ≫
        (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D Q)).hom =
      (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D P)).hom ≫
        Functor.whiskerLeft (scalarModuleExtensionHomotopy φ D)
          (kernelTensorHomotopyMap A' (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)) := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (scalarModuleExtensionHomotopy φ E).map
      ((kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M)) ≫
      (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D Q)).hom.app
        ((moduleToHomotopy A D).obj M) =
    (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D P)).hom.app
        ((moduleToHomotopy A D).obj M) ≫
      (kernelTensorHomotopyMap A' (DGBaseChange φ D) (DGBaseChange φ E)
        ((scalarKernelFunctor φ D E).map f)).app
        ((moduleToHomotopy A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj M))
  rw [kernelTensorHomotopyMap_app, scalarKernelExtensionHomotopy_map_closed,
    scalarKernelBalancedHomotopyIso_app, scalarKernelBalancedHomotopyIso_app,
    kernelTensorHomotopyMap_app, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg (moduleToHomotopy A' (DGBaseChange φ E)).map
    (scalarKernelBalancedIso_kernel_naturality φ D E f M)

lemma scalarKernelBalancedHomotopyDerivedIso_kernel_naturality
    {P Q : BimoduleCategory A E D} (f : P ⟶ Q) :
    Functor.whiskerRight (kernelTensorHomotopyMap A D E f)
        (moduleExtensionHomotopyToDerived φ E) ≫
        (scalarKernelBalancedHomotopyDerivedIso φ D E (BimoduleCategory.underlying A E D Q)).hom =
      (scalarKernelBalancedHomotopyDerivedIso φ D E (BimoduleCategory.underlying A E D P)).hom ≫
        Functor.whiskerLeft (scalarModuleExtensionHomotopy φ D)
          (Functor.whiskerRight
            (kernelTensorHomotopyMap A' (DGBaseChange φ D) (DGBaseChange φ E)
              ((scalarKernelFunctor φ D E).map f))
            (moduleHomotopyToDerivedClosed A' (DGBaseChange φ E))) := by
  apply NatTrans.ext
  funext X
  simp only [scalarKernelBalancedHomotopyDerivedIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc]
  erw [(scalarExtensionHomotopyDerivedIso φ E).inv.naturality
    ((kernelTensorHomotopyMap A D E f).app X)]
  simp only [Functor.comp_map, Category.assoc]
  have h := congrArg (moduleHomotopyToDerivedClosed A' (DGBaseChange φ E)).map
    (NatTrans.congr_app (scalarKernelBalancedHomotopyIso_kernel_naturality φ D E f) X)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_comp] at h
  exact congrArg (fun k => (scalarExtensionHomotopyDerivedIso φ E).inv.app
    (((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onHomotopy).obj X) ≫ k) h

end SerrePositivity.DifferentialGraded.Morita
