module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffinePolynomialTor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedForms
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TorAcyclicFiniteBasis

/-!
# 元の完備形式の被覆へのTor消滅

## 概要
元の完備形式は、指定被覆への係数拡大で高次Torを持たない。

## 方針
元の有限自由な外積座標基底を使い、元の完備多項式係数加群の検証済みTor消滅へ戻す。

## 規約
元のaffine係数作用と元の基底への制限を使う。一般の結晶比較は入力にしない。

## 使われ方
元のηの始域のsame singleの導来係数拡大を計算する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion DifferentialGraded DifferentialGraded.ScalarExtension HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

include hP
/-- 元の完備形式の元の基底作用への制限は、被覆への高次Torが消える。 -/
theorem affineRestrictedForms_scalarExtensionTorVanishing (i : ℕ) :
    scalarExtensionTorVanishing (Construction61.crystallineCoverMap P).toRingHom
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
        (ModuleCat.of (affineAlgebra P r) (affineForms P r i))) := by
  letI : Fintype (Set.powersetCard (formVars.{u} r) i) := Fintype.ofFinite _
  exact scalarExtensionTorVanishing_of_finiteBasis (Construction61.crystallineCoverMap P).toRingHom
    (affineBaseToPolynomialMap P r) (affineRestrictedAlgebra_scalarExtensionTorVanishing P hP r)
      (ModuleCat.of (affineAlgebra P r) (affineForms P r i)) (affineFormsCoordinateBasis P r i)

/-- 元の形式の零次数singleへの標準非有界導来増大は、被覆に沿って同型。 -/
theorem affineRestrictedForms_nativeAugmentation_isIso (i : ℕ) :
    IsIso ((complexDerivedExtensionAugmentation (Construction61.crystallineCoverMap P).toRingHom).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
          (ModuleCat.of (affineAlgebra P r) (affineForms P r i))))) :=
  nativeDerivedAugmentation_isIso_of_torVanishing _ _
    (affineRestrictedForms_scalarExtensionTorVanishing P hP r i)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
