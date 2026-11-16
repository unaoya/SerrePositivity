module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoverUnitMap
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullRowComplete
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PairCompletionExtension
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineDerivedCoefficientRows
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 元のfull envelopeの指定同型は元の係数増大の完備延長

## 概要
元の指定被覆同型は、元の標準係数増大の二回完備化に沿う延長と一致する。

## 方針
元の二つの単位上の射の一致と、完備な終域への延長の一意性を使う。

## 規約
指定同型を延長から再定義せず、その同じ射の等式を証明する。

## 使われ方
R1の剰余行の指定同型を同じ係数増大から特徴づける。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元のfull envelopeの指定被覆同型は、元の係数増大の同じ完備延長。 -/
theorem affineFullCoverTermIso_eq_extension
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineFullBaseModules P hP r).obj n
    let N := (affineFullBaseModules Q hQ r).obj n
    let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    let hc := affineFullBaseModules_complete_p Q hQ r n
    (affineFullCoverTermIso P hP r n).hom =
      pairCompletionExtension (p : B) (p : B) Y
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) hc hc
        (affineDerivedFullCoefficientMap (Construction61.crystallineCoverMap P) hP hQ r n) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineFullBaseModules P hP r).obj n
  let N := (affineFullBaseModules Q hQ r).obj n
  let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  let hc := affineFullBaseModules_complete_p Q hQ r n
  apply pairCompletionExtension_ext (p : B) (p : B) Y
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) hc hc
  rw [affineFullCoverTermIso_unit P hP r n, pairCompletionExtension_unit]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
