module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBalancedNaturality
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHomotopy
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension

/-! # kernel係数変更比較のH⁰降下と主導来値への接続 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 通常入力上で、二つのH⁰関手の前合成を実際の加群比較で同定する。 -/
def scalarKernelBalancedHomotopyFacIso :
    moduleToHomotopy A D ⋙ (kernelTensor A D E P).onHomotopy ⋙
        scalarModuleExtensionHomotopy φ E ≅
      moduleToHomotopy A D ⋙ scalarModuleExtensionHomotopy φ D ⋙
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onHomotopy :=
  Functor.isoWhiskerRight (eqToIso (kernelTensor A D E P).onHomotopy_fac)
      (scalarModuleExtensionHomotopy φ E) ≪≫
    Functor.isoWhiskerLeft (kernelTensor A D E P).onClosed
      (eqToIso (scalarModuleExtensionHomotopy_fac φ E)) ≪≫
    Functor.isoWhiskerRight (scalarKernelBalancedNatIso φ D E P)
      (moduleToHomotopy A' (DGBaseChange φ E)) ≪≫
    Functor.isoWhiskerLeft (moduleExtension φ D)
      (eqToIso (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).onHomotopy_fac).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (scalarModuleExtensionHomotopy_fac φ D)).symm
      (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onHomotopy

/-- 全てのH⁰入力射に自然な、係数変更とkernel作用の比較。 -/
def scalarKernelBalancedHomotopyIso :
    (kernelTensor A D E P).onHomotopy ⋙ scalarModuleExtensionHomotopy φ E ≅
      scalarModuleExtensionHomotopy φ D ⋙
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onHomotopy :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (scalarKernelBalancedHomotopyFacIso φ D E P)

/-- 既存の二つの係数変更ホモトピー関手は、主導来値へ送ると自然に一致する。 -/
def scalarExtensionHomotopyDerivedIso :
    scalarModuleExtensionHomotopy φ D ⋙ moduleHomotopyToDerivedClosed A' (DGBaseChange φ D) ≅
      moduleExtensionHomotopyToDerived φ D :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (Functor.isoWhiskerRight (eqToIso (scalarModuleExtensionHomotopy_fac φ D))
        (moduleHomotopyToDerivedClosed A' (DGBaseChange φ D)) ≪≫
      Functor.isoWhiskerLeft (moduleExtension φ D)
        (moduleToHomotopyDerivedIso A' (DGBaseChange φ D)) ≪≫
      (eqToIso (moduleExtensionHomotopyToDerived_fac φ D)).symm)

/-- H⁰のkernel係数変更比較を、実際の主導来値の関手へ送る。 -/
def scalarKernelBalancedHomotopyDerivedIso :
    (kernelTensor A D E P).onHomotopy ⋙ moduleExtensionHomotopyToDerived φ E ≅
      scalarModuleExtensionHomotopy φ D ⋙
        kernelHomotopyToDerived A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) :=
  Functor.isoWhiskerLeft (kernelTensor A D E P).onHomotopy
      (scalarExtensionHomotopyDerivedIso φ E).symm ≪≫
    Functor.isoWhiskerRight (scalarKernelBalancedHomotopyIso φ D E P)
      (moduleHomotopyToDerivedClosed A' (DGBaseChange φ E))

end SerrePositivity.DifferentialGraded.Morita
