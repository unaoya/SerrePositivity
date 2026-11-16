module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoverExtension
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverProjectionEpi
public import SerrePositivity.HomologicalAlgebra.DerivedNonpositiveHom

/-!
# 元の剰余被覆同型は元の係数増大の完備延長

## 概要
元の剰余行の指定被覆同型は、元の標準係数増大の二回完備化に沿う延長と一致する。

## 方針
元の商射の正方形をfull envelopeの一致と合わせ、H⁰上の全射性で降ろす。

## 規約
元の指定同型を保持し、導来圏の商射をエピ射とは仮定しない。

## 使われ方
R1の元のκの項ごとの指定された射の一致を得る。
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

/-- 元の剰余被覆同型は、元の標準係数増大の同じ完備延長。 -/
theorem affineReducedCoverTermIso_eq_extension
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineBaseModules P hP r).obj n
    let N := (affineBaseModules Q hQ r).obj n
    let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    let hc := affineBaseModules_complete Q hQ r n
    (affineReducedCoverTermIso P hP r n).hom =
      pairCompletionExtension (p : B) (p : B) Y
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) hc hc
        (affineDerivedReducedCoefficientMap (Construction61.crystallineCoverMap P) hP hQ r n) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let f := Construction61.crystallineCoverMap P
  let α := f.toRingHom
  let C := derivedComplexCompletionFunctor B (p : B)
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} B) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let M₀ := (affineFullBaseModules P hP r).obj n
  let M₁ := (affineBaseModules P hP r).obj n
  let N₀ := (affineFullBaseModules Q hQ r).obj n
  let N₁ := (affineBaseModules Q hQ r).obj n
  let X₀ := boundedAboveDerivedSingleFunctor.obj M₀
  let X₁ := boundedAboveDerivedSingleFunctor.obj M₁
  let Y₀ := ((boundedAboveDerivedBaseChange α).obj X₀).obj
  let Y₁ := ((boundedAboveDerivedBaseChange α).obj X₁).obj
  let q₀ : Y₀ ⟶ Y₁ := ((boundedAboveDerivedBaseChange α).map
    (boundedAboveDerivedSingleFunctor.map ((affineFullBaseProjection P hP r).app n))).hom
  let q := C.map (C.map q₀)
  let π := S.map ((affineFullBaseProjection Q hQ r).app n)
  let h₀ := affineFullBaseModules_complete_p Q hQ r n
  let h₁ := affineBaseModules_complete Q hQ r n
  let a₀ := affineDerivedFullCoefficientMap f hP hQ r n
  let a₁ := affineDerivedReducedCoefficientMap f hP hQ r n
  let e₁ := pairCompletionExtension (p : B) (p : B) Y₁ (S.obj N₁) h₁ h₁ a₁
  have hcan : q ≫ e₁ = (affineFullCoverTermIso P hP r n).hom ≫ π := by
    calc
      _ = pairCompletionExtension (p : B) (p : B) Y₀ (S.obj N₁) h₁ h₁ (q₀ ≫ a₁) :=
        pairCompletionExtension_precomp (p : B) (p : B) h₁ h₁ q₀ a₁
      _ = pairCompletionExtension (p : B) (p : B) Y₀ (S.obj N₁) h₁ h₁ (a₀ ≫ π) := by
        congr 1
        exact affineDerivedCoefficientMap_projection f hP hQ r n
      _ = pairCompletionExtension (p : B) (p : B) Y₀ (S.obj N₀) h₀ h₀ a₀ ≫ π :=
        (pairCompletionExtension_postcomp (p : B) (p : B) h₀ h₀ h₁ h₁ a₀ π).symm
      _ = _ := by rw [← affineFullCoverTermIso_eq_extension P hP r n]
  let : X₁.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M₁).IsLE 0
    infer_instance
  let : Y₁.IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars α) X₁ 0
  let : (C.obj Y₁).IsLE 0 := derivedComplexCompletionFunctor_isLE B (p : B) Y₁ 0 inferInstance
  let : (C.obj (C.obj Y₁)).IsLE 0 :=
    derivedComplexCompletionFunctor_isLE B (p : B) (C.obj Y₁) 0 inferInstance
  haveI : Epi (H.map q) := affineFullBaseProjection_cover_homology_epi P hP r n
  apply (derivedNonpositiveHomologyZero_map_bijective
    (X := C.obj (C.obj Y₁)) (Y := S.obj N₁)).injective
  apply (cancel_epi (H.map q)).mp
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg H.map
  exact (affineReducedCoverTermIso_projection P hP r n).trans hcan.symm

/-- 元の剰余被覆同型は、元の二つの単位上で同じ標準係数増大。 -/
theorem affineReducedCoverTermIso_unit
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineBaseModules P hP r).obj n
    let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    ((derivedComplexCompletionUnit B (p : B)).app Y ≫
      (derivedComplexCompletionUnit B (p : B)).app
        ((derivedComplexCompletionFunctor B (p : B)).obj Y)) ≫
      (affineReducedCoverTermIso P hP r n).hom =
    affineDerivedReducedCoefficientMap (Construction61.crystallineCoverMap P) hP
      (Construction61.crystallineCover_bounded P) r n := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineBaseModules P hP r).obj n
  let N := (affineBaseModules Q hQ r).obj n
  let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  let hc := affineBaseModules_complete Q hQ r n
  rw [affineReducedCoverTermIso_eq_extension P hP r n]
  exact pairCompletionExtension_unit (p : B) (p : B) Y
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) hc hc
    (affineDerivedReducedCoefficientMap (Construction61.crystallineCoverMap P) hP hQ r n)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
