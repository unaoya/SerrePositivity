module
public import SerrePositivity.DifferentialGraded.Morita.KernelDerivedFunctor

/-! # 対角kernelの主導来作用と恒等関手

## 概要
対角bimoduleのtensor単位子と入力解像度の増大射から、主導来作用の恒等比較を構成する。

## 方針
通常単位子をH⁰へ降ろし、入力解像度関手の増大を局所化の普遍性で恒等関手へ比較する。

## 規約と注意
DのSmall.{u}だけを要求し、localHomKFlatは不要。一般の分解変更coherenceは扱わない。

## 使われ方
U16aのkernelIdentityIsoと、以後の合成比較の単位整合性で使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 対角kernelの通常作用は、既存の全Hom自然な左単位子によって恒等と比較される。 -/
def kernelIdentityClosedIso :
    (kernelTensor A D D (Bimodule.diagonal A D)).onClosed ≅ 𝟭 (ModuleCategory A D) :=
  NatIso.ofComponents (fun M =>
    (BimoduleCategory.evaluation A D (RightModule A D) (ForgetEnrichment.to (Complex A) M)).mapIso
      (leftBimoduleUnitIso A D (RightModule A D) (DGFunctor.id (RightModule A D))))
    (fun f => (kernelClosedFamilyNatTrans A D (RightModule A D)
      (leftBimoduleUnitIso A D (RightModule A D)
        (DGFunctor.id (RightModule A D))).hom).naturality f)

/-- 対角kernelの通常単位子をH⁰商へ降ろした自然同型。 -/
def kernelIdentityHomotopyIso :
    (kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy ≅
      𝟭 (ModuleHomotopyCategory A D) :=
  CategoryTheory.Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (eqToIso (kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy_fac ≪≫
      Functor.isoWhiskerRight (kernelIdentityClosedIso A D) (moduleToHomotopy A D) ≪≫
      Functor.leftUnitor (moduleToHomotopy A D) ≪≫
      (Functor.rightUnitor (moduleToHomotopy A D)).symm)

/-- 指定入力解像度族の増大射は、持ち上げのH⁰可換squareにより自然変換になる。 -/
def kernelInputResolutionHomotopyAugmentation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⟶ moduleToHomotopy A D where
  app M := (moduleToHomotopy A D).map (R M).π
  naturality {M N} f := (R M).lift_fac (R N) f

/-- 入力増大は準同型なので、主導来圏では解像度族と元の入力を自然同型で結ぶ。 -/
def kernelInputResolutionDerivedAugmentationIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⋙ moduleHomotopyToDerivedClosed A D ≅
      moduleToDerived A D := by
  let τ := whiskerRight (kernelInputResolutionHomotopyAugmentation A D R)
    (moduleHomotopyToDerivedClosed A D)
  have ht : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Localization.inverts (moduleHomotopyToDerivedClosed A D)
      (moduleHomotopyQuasiIso A D) _
      ((moduleHomotopyQuasiIso_map_iff A D (R M).π).2 (R M).quasiIso)
  let := ht
  exact asIso τ ≪≫ moduleToHomotopyDerivedIso A D

/-- 同じ入力解像度の増大を全主導来入力へ延長した、実際の解像度関手の余単位同型。 -/
def kernelInputResolutionDerivedCounitIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionFunctor A D R ⋙ moduleHomotopyToDerivedClosed A D ≅
      𝟭 (DerivedModuleCategory A D) := by
  let G := moduleDerivedResolutionFunctor A D R ⋙ moduleHomotopyToDerivedClosed A D
  let e : moduleToDerived A D ⋙ G ≅ moduleToDerived A D :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A D R)
        (moduleHomotopyToDerivedClosed A D) ≪≫
      kernelInputResolutionDerivedAugmentationIso A D R
  exact Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleToDerived A D ⋙ G) (moduleToDerived A D) G (𝟭 _) e

/-- 通常の対角kernelの導来作用を、H⁰単位子と入力解像度増大から恒等へ比較する。 -/
def kernelDerivedTensorOnBimoduleIdentityIso :
    kernelDerivedTensorOnBimodule A D D (Bimodule.diagonal A D) ≅
      𝟭 (DerivedModuleCategory A D) :=
  Functor.isoWhiskerLeft
      (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D))
      (Functor.isoWhiskerRight (kernelIdentityHomotopyIso A D)
          (moduleHomotopyToDerivedClosed A D) ≪≫
        Functor.leftUnitor (moduleHomotopyToDerivedClosed A D)) ≪≫
    kernelInputResolutionDerivedCounitIso A D (moduleCanonicalProjectiveResolution A D)

/-- 主導来対角kernelの作用は恒等関手と自然同型。必要仮定はSmall.{u} Dのみ。 -/
def kernelIdentityIso :
    kernelDerivedTensor A D D (kernelIdentity A D) ≅ 𝟭 (DerivedModuleCategory A D) :=
  kernelDerivedTensorOnBimoduleIso A D D
      (BimoduleCategory.of A D D (Bimodule.diagonal A D)) ≪≫
    kernelDerivedTensorOnBimoduleIdentityIso A D

end SerrePositivity.DifferentialGraded.Morita
