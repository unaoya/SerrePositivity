module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoverTerms
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineEnvelopeTargetH0Unit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullTensorCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoverTerms
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullTensorCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange

/-!
# 元のfull envelopeの被覆同型と元の係数増大

## 概要
元の指定被覆同型は、二つの元の完備化単位上で元の通常係数増大と一致する。

## 方針
同じ選択された環同型によるH⁰の単位の式を、元の通常係数射の式へ移す。

## 規約
既存のaffineFullCoverTermIsoを変更しない。

## 使われ方
元の剰余被覆同型とκの各項の一致を、元の商射を介して証明する。
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
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元のfull envelopeの指定同型の二つの単位上のH⁰は、同じ元の係数増大。 -/
theorem affineFullCoverTermIso_unit_homology
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineFullBaseModules P hP r).obj n
    let N := (affineFullBaseModules Q hQ r).obj n
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
    let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    H.map (((derivedComplexCompletionUnit B (p : B)).app Y ≫
        (derivedComplexCompletionUnit B (p : B)).app
          ((derivedComplexCompletionFunctor B (p : B)).obj Y)) ≫
        (affineFullCoverTermIso P hP r n).hom) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).hom.app N =
    H.map ((boundedAboveDerivedBaseChangeModuleAugmentation α).app M) ≫
      (realizedSingleH0Iso B).hom.app ((ModuleCat.extendScalars α).obj M) ≫
      (affineFullAnyOrdinaryMap (Construction61.crystallineCoverMap P) hP hQ r).app n := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let f := Construction61.crystallineCoverMap P
  let α := f.toRingHom
  let M := (affineFullBaseModules P hP r).obj n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let z := H.map ((boundedAboveDerivedBaseChangeModuleAugmentation α).app M) ≫
    (realizedSingleH0Iso B).hom.app ((ModuleCat.extendScalars α).obj M)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let := α.toAlgebra
  let U := affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl
  let := U.X.toHom.toRingHom.toAlgebra
  have hu := affineEnvelopeTargetH0_unit P Q hP hQ f r n.len
    (cutoff A (affineAlgebra P r)) (cutoff B (affineAlgebra Q r)) le_rfl le_rfl x
  have ht := affineFullTensorCoefficients f hP hQ r n (z x)
  let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  let u := (derivedComplexCompletionUnit B (p : B)).app Y ≫
    (derivedComplexCompletionUnit B (p : B)).app ((derivedComplexCompletionFunctor B (p : B)).obj Y)
  let e := (affineFullCoverTermIso P hP r n).hom
  let c := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).hom.app
    ((affineFullBaseModules Q hQ r).obj n)
  calc
    _ = ((H.map u ≫ H.map e) ≫ c) x :=
      congrArg (fun k => (k ≫ c) x) (H.map_comp u e)
    _ = _ := hu.trans ht

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
