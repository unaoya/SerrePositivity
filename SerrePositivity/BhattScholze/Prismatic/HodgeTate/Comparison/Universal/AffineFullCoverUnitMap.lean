module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoverUnit
public import SerrePositivity.HomologicalAlgebra.DerivedNonpositiveHom
public import SerrePositivity.HomologicalAlgebra.RealizedSingleH0Normalization

/-!
# 元のfull envelopeの指定被覆同型と係数増大の射の一致

## 概要
元の二つの完備化単位の後の指定同型は、元の標準導来底変換の係数増大そのもの。

## 方針
非正次数から離散対象へのH⁰の忠実性と、元のH⁰正規化の一致を使う。

## 規約
比較同型も標準増大も変更しない。

## 使われ方
元の剰余行の指定同型とκの項ごとの射を照合する。
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

/-- 元のfull envelopeの指定同型は元の二つの単位上で標準係数増大そのもの。 -/
theorem affineFullCoverTermIso_unit
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let hQ := Construction61.crystallineCover_bounded P
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineFullBaseModules P hP r).obj n
    let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    ((derivedComplexCompletionUnit B (p : B)).app Y ≫
      (derivedComplexCompletionUnit B (p : B)).app
        ((derivedComplexCompletionFunctor B (p : B)).obj Y)) ≫
      (affineFullCoverTermIso P hP r n).hom =
    (boundedAboveDerivedBaseChangeModuleAugmentation α).app M ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
        ((affineFullAnyOrdinaryMap (Construction61.crystallineCoverMap P) hP hQ r).app n) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineFullBaseModules P hP r).obj n
  let N := (affineFullBaseModules Q hQ r).obj n
  let X := boundedAboveDerivedSingleFunctor.obj M
  let Y := ((boundedAboveDerivedBaseChange α).obj X).obj
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} B) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0
  let g := (affineFullAnyOrdinaryMap (Construction61.crystallineCoverMap P) hP hQ r).app n
  let : X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M).IsLE 0
    infer_instance
  let : Y.IsLE 0 := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars α) X 0
  apply (derivedNonpositiveHomologyZero_map_bijective (X := Y) (Y := S.obj N)).injective
  apply (cancel_mono (ε.hom.app N)).mp
  have hn := ε.hom.naturality g
  change H.map (S.map g) ≫ ε.hom.app N = ε.hom.app _ ≫ g at hn
  rw [affineFullCoverTermIso_unit_homology P hP r n]
  let a := (boundedAboveDerivedBaseChangeModuleAugmentation α).app M
  change H.map a ≫ (realizedSingleH0Iso B).hom.app ((ModuleCat.extendScalars α).obj M) ≫ g =
    H.map (a ≫ S.map g) ≫ ε.hom.app N
  have hm := H.map_comp a (S.map g)
  rw [hm, Category.assoc, hn]
  rw [realizedSingleH0Iso_hom_eq_standard ((ModuleCat.extendScalars α).obj M)]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
