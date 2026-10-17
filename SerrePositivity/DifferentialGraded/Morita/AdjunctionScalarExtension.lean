module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionSquare
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelLocalizedSquare

/-! # 局所化kernel係数変更と実際のMorita右随伴

## 概要
既存の条件付き係数変更正方形を、元と変更後の実際の一般右随伴へ接続する。

## 方針
scalarKernelLocalizedDerivedSquareを、実際の単位・余単位による右随伴正方形へ転置する。

## 規約と注意
両kernel作用の同値性、通常代表、hα・hAug・hP'を保持する。
係数変更後のMorita性を無条件に結論しない。未完のU12f成分同定・kernel合成比較は代用しない。

## 使われ方
U16cの一般右随伴を、U16dの実際の局所化係数変更正方形に適用する入口。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : BimoduleCategory A E D)
  (hα : IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P))
  (hAug : ∀ M : ModuleCategory A D,
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onClosed.obj
        (moduleCanonicalProjectiveResolution A D M).obj)))
  (hP' : ∀ M : ModuleCategory A D,
    moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A)
        (moduleCanonicalProjectiveResolution A D M).obj)))
variable [(kernelDerivedTensor A D E ((bimoduleToDerived A E D).obj P)).IsEquivalence]
  [(kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
    ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))).IsEquivalence]

/-- 実際の局所化kernelの係数変更正方形から得る、一般右随伴側の比較。 -/
def kernelRightAdjointLocalizedBaseChangeIso :
    kernelDerivedHom A D E ((bimoduleToDerived A E D).obj P) ⋙ derivedExtension φ D ≅
      derivedExtension φ E ⋙
        kernelDerivedHom A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P)) :=
  kernelRightAdjointSquareIso A D E A' (DGBaseChange φ D) (DGBaseChange φ E)
    ((bimoduleToDerived A E D).obj P)
    ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
    (derivedExtension φ D) (derivedExtension φ E)
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP')

/-- 係数変更の右随伴比較は、実際の余単位で既存の左作用正方形へ戻る。 -/
lemma kernelRightAdjointLocalizedBaseChangeIso_counit (Y : DerivedModuleCategory A E) :
    (kernelDerivedTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
      ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))).map
        ((kernelRightAdjointLocalizedBaseChangeIso φ D E P hα hAug hP').hom.app Y) ≫
      (kernelDerivedCounit A' (DGBaseChange φ D) (DGBaseChange φ E)
        ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))).app
        ((derivedExtension φ E).obj Y) =
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP').inv.app
        ((kernelDerivedHom A D E ((bimoduleToDerived A E D).obj P)).obj Y) ≫
      (derivedExtension φ E).map
        ((kernelDerivedCounit A D E ((bimoduleToDerived A E D).obj P)).app Y) :=
  kernelRightAdjointSquareIso_counit A D E A' (DGBaseChange φ D) (DGBaseChange φ E)
    ((bimoduleToDerived A E D).obj P)
    ((scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P))
    (derivedExtension φ D) (derivedExtension φ E)
    (scalarKernelLocalizedDerivedSquare φ D E P hα hAug hP') Y

end SerrePositivity.DifferentialGraded.Morita
