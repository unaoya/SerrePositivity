module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedConeRightLeg
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PairScalarConeRightLeg
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverTerms
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BoundedScalarConeRightLeg

/-!
# 元の剰余被覆同型と元の商射の正方形

## 概要
指定された剰余被覆同型は、元のfull envelopeの被覆同型と商射を結ぶ。

## 方針
元の右脚の三つの法則と、元の錐関手の右脚の自然性を順に合成する。

## 規約
剰余被覆同型を再定義せず、元のaffineReducedCoverTermIsoを使う。

## 使われ方
元の係数比較をfull envelopeから剰余行へ降ろす。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- 座標の同じ等式による錐の移送は元の右脚を保つ。 -/
theorem derivedScalarConeRightLeg_eqToHom {R : Type u} [CommRing R]
    {a b : R} (h : a = b) (X : DerivedCategory (ModuleCat.{u} R)) :
    (derivedScalarConeRightLeg R a).app X ≫
      eqToHom (congrArg (fun t => (derivedScalarConeFunctor R t).obj X) h) =
      (derivedScalarConeRightLeg R b).app X := by
  subst b
  simp

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の指定された被覆比較は元のfull envelopeの商射を保つ。 -/
theorem affineReducedCoverTermIso_projection
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let G := boundedAboveDerivedBaseChange (Construction61.crystallineCoverMap P).toRingHom ⋙
      boundedAboveDerivedCompletionFunctor B (p : B) ⋙
      boundedAboveDerivedCompletionFunctor B (p : B)
    (G.map (boundedAboveDerivedSingleFunctor.map ((affineFullBaseProjection P hP r).app n))).hom ≫
      (affineReducedCoverTermIso P hP r n).hom =
    (affineFullCoverTermIso P hP r n).hom ≫
      (moduleObjectFunctor B).map ((affineFullBaseProjection Q hQ r).app n) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let X := boundedAboveDerivedSingleFunctor.obj ((affineFullBaseModules P hP r).obj n)
  let M := (affineFullBaseModules Q hQ r).obj n
  let G := boundedAboveDerivedBaseChange α ⋙ boundedAboveDerivedCompletionFunctor B (p : B) ⋙
    boundedAboveDerivedCompletionFunctor B (p : B)
  let eR : (boundedAboveDerivedScalarCone A P.generator).obj X ≅
      boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n) :=
    ObjectProperty.isoMk _ (affineReducedScalarConeIso P hP r n)
  let v := (Construction61.crystallineCoverMap P).existsUnique_generator_unit.choose
  have hv : α P.generator = (p : B) * (v : B) :=
    (Construction61.crystallineCoverMap P).existsUnique_generator_unit.choose_spec.1
  have hp : boundedAboveDerivedSingleFunctor.map ((affineFullBaseProjection P hP r).app n) =
      boundedScalarConeRightLeg P.generator X ≫ eR.hom := by
    apply ObjectProperty.hom_ext
    exact (affineReducedScalarConeIso_rightLeg P hP r n).symm
  have hpair := pairCompletedScalarConeIso_rightLeg α P.generator (p : B) (p : B) X
  have hn := (derivedScalarConeRightLeg B (α P.generator)).naturality
    (affineFullCoverTermIso P hP r n).hom
  simp only [Functor.id_map] at hn
  have heq := derivedScalarConeRightLeg_eqToHom hv ((moduleObjectFunctor B).obj M)
  have hor := derivedScalarConeOrientationSingleIso_rightLeg (p : B) v M
  have hquot := affineReducedScalarConeIso_rightLeg Q hQ r n
  have htail : (derivedScalarConeRightLeg B (α P.generator)).app ((moduleObjectFunctor B).obj M) ≫
      eqToHom (congrArg (fun b => (derivedScalarConeFunctor B b).obj ((moduleObjectFunctor B).obj M)) hv) ≫
      (derivedScalarConeOrientationSingleIso (p : B) v M).hom ≫
      (affineReducedScalarConeIso Q hQ r n).hom =
      (moduleObjectFunctor B).map ((affineFullBaseProjection Q hQ r).app n) := by
    calc
      _ = (derivedScalarConeRightLeg B ((p : B) * (v : B))).app ((moduleObjectFunctor B).obj M) ≫
          (derivedScalarConeOrientationSingleIso (p : B) v M).hom ≫
          (affineReducedScalarConeIso Q hQ r n).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (derivedScalarConeOrientationSingleIso (p : B) v M).hom ≫
            (affineReducedScalarConeIso Q hQ r n).hom) heq
      _ = (derivedScalarConeRightLeg B (p : B)).app ((moduleObjectFunctor B).obj M) ≫
          (affineReducedScalarConeIso Q hQ r n).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (affineReducedScalarConeIso Q hQ r n).hom) hor
      _ = _ := hquot
  change (G.map (boundedAboveDerivedSingleFunctor.map
    ((affineFullBaseProjection P hP r).app n))).hom ≫ _ = _
  rw [hp, Functor.map_comp]
  simp only [affineReducedCoverTermIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv,
    ObjectProperty.ι_map]
  change ((G.map (boundedScalarConeRightLeg P.generator X)).hom ≫ (G.map eR.hom).hom) ≫
    ((G.map eR.inv).hom ≫ (pairCompletedScalarConeIso α P.generator (p : B) (p : B) X).hom ≫
      (derivedScalarConeFunctor B (α P.generator)).map (affineFullCoverTermIso P hP r n).hom ≫
      eqToHom (congrArg (fun b => (derivedScalarConeFunctor B b).obj
        ((moduleObjectFunctor B).obj M)) hv) ≫ (derivedScalarConeOrientationSingleIso (p : B) v M).hom ≫
      (affineReducedScalarConeIso Q hQ r n).hom) = _
  have heR : (G.map eR.hom).hom ≫ (G.map eR.inv).hom = 𝟙 _ := by
    exact congrArg (fun q => q.hom) (G.mapIso eR).hom_inv_id
  simp only [Category.assoc]
  rw [← Category.assoc (G.map eR.hom).hom, heR, Category.id_comp]
  rw [← Category.assoc, hpair, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  exact congrArg (fun k => (affineFullCoverTermIso P hP r n).hom ≫ k) htail

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
