module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsTor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BiprodDerivedAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineModelsComplete

/-!
# 元のaffine lineの形式の直和と被覆への標準導来増大

## 概要
元のηの始域について、同じ基底作用への制限と標準導来増大を計算する。

## 方針
元の係数制限の直和・singleの同型で零次と一次へ戻し、元の形式のTor消滅を使う。

## 規約
元の始域自体のK-flat性を入力にしない。元の二つの次数と元の直和を維持する。

## 使われ方
元のηの被覆像の始域を、同じ通常係数拡大の二次数模型へ接続する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] additive_preservesBinaryBiproducts_model
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A)

/-- 元の形式の直和の係数制限を、同じ二つの次数の係数制限した形式へ移す。 -/
def affineLineFormalRestrictionIso :
    affineComplexOnBase P 1 (affineLineFormalModel P) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
          (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 0))) ⊞
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 1).obj
        ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
          (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 1))) := by
  let U := ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)
  exact (U.mapHomologicalComplex (.up ℤ)).mapBiprod _ _ ≪≫
    biprod.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
        (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 0)))
      ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 1).app
        (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 1)))

variable (hP : IsBoundedPrism P)
include hP
/-- 元のηの元の始域への、指定被覆に沿う標準非有界導来増大は同型。 -/
theorem affineLineFormalCover_nativeAugmentation_isIso :
    IsIso ((complexDerivedExtensionAugmentation (Construction61.crystallineCoverMap P).toRingHom).app
      (affineComplexOnBase P 1 (affineLineFormalModel P))) := by
  let f := (Construction61.crystallineCoverMap P).toRingHom
  let U := ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)
  let M₀ := U.obj (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 0))
  let M₁ := U.obj (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 1))
  let K₀ := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M₀
  let K₁ := (CochainComplex.singleFunctor (ModuleCat.{u} A) 1).obj M₁
  haveI := nativeDerivedAugmentation_singleDegree_isIso f M₀
    (affineRestrictedForms_scalarExtensionTorVanishing P hP 1 0) 0
  haveI := nativeDerivedAugmentation_singleDegree_isIso f M₁
    (affineRestrictedForms_scalarExtensionTorVanishing P hP 1 1) 1
  haveI := nativeDerivedAugmentation_biprod_isIso f K₀ K₁
  exact nativeDerivedAugmentation_isIso_of_iso f (affineLineFormalRestrictionIso P)

/-- 同じ元の始域の指定半自由増大は、被覆への係数拡大後も擬同型。 -/
theorem affineLineFormalCover_resolvedAugmentation_quasiIso :
    QuasiIso (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ)).map ((complexResolutionAugmentation A).app
        (affineComplexOnBase P 1 (affineLineFormalModel P)))) := by
  haveI := affineLineFormalCover_nativeAugmentation_isIso P hP
  exact nativeResolutionAugmentation_baseChange_quasiIso _ _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
