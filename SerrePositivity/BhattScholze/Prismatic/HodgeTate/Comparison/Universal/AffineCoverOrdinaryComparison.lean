module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineFormalCoverAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineBaseChangeComplete
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ResolvedOrdinaryComparison

/-!
# 元の指定被覆模型から同じ通常係数拡大への自然な比較

## 概要
元のaffine複体について、同じ指定半自由増大と元の完備化単位を使う比較を束ねる。

## 方針
標準増大の自然性と、通常係数拡大の完備性から得る標準単位の逆を合成する。

## 規約
一般の元の複体で比較が同型だとは仮定しない。元のηの始域での同型性はTor消滅から与える。

## 使われ方
元のηの被覆像の図式を、同じ通常係数拡大の図式へ移す。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonTotal HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (r : ℕ)

/-- 元のaffine作用から元の基底作用への同じ制限。 -/
abbrev affineRestrictedComplexFunctor :=
  (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).mapHomologicalComplex (.up ℤ)

/-- 同じ元の基底作用へ制限してから通常の被覆係数拡大をする関手。 -/
abbrev affineOrdinaryCoverFunctor := affineRestrictedComplexFunctor P r ⋙
  (ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ)

/-- 同じ元の基底作用へ制限してから完備被覆係数拡大をする関手。 -/
abbrev affineCompletedCoverFunctor :=
  affineRestrictedComplexFunctor P r ⋙ Construction61.completedCoverModelFunctor P

/-- 同じ元の基底作用への制限の指定半自由模型を完備被覆関手で写す関手。 -/
abbrev affineResolvedCoverFunctor := affineRestrictedComplexFunctor P r ⋙ complexResolutionFunctor A ⋙
  Construction61.completedCoverModelFunctor P

/-- 元の指定分解の増大と標準完備化単位だけからなる自然な比較。 -/
def affineCoverOrdinaryComparison :
    affineResolvedCoverFunctor P r ⋙ DerivedCategory.Q ⟶
      affineOrdinaryCoverFunctor P r ⋙ DerivedCategory.Q :=
  resolvedOrdinaryComparison (Construction61.crystallineCoverMap P).toRingHom
    (fun _ : Fin 2 => (p : Construction61.crystallineCoverRing P))
    (affineRestrictedComplexFunctor P r) (fun K _ => affineCoverBaseChange_complete_p P r K)

/-- 元のηの元の始域では、同じ自然な比較が同型となる。 -/
theorem affineLineFormalCoverOrdinaryComparison_isIso (hP : IsBoundedPrism P) :
    IsIso ((affineCoverOrdinaryComparison P 1).app (affineLineFormalModel P)) :=
  resolvedOrdinaryComparison_app_isIso (Construction61.crystallineCoverMap P).toRingHom
    (fun _ : Fin 2 => (p : Construction61.crystallineCoverRing P))
    (affineRestrictedComplexFunctor P 1) (fun K _ => affineCoverBaseChange_complete_p P 1 K)
    (affineLineFormalModel P) (affineLineFormalCover_resolvedAugmentation_quasiIso P hP)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
