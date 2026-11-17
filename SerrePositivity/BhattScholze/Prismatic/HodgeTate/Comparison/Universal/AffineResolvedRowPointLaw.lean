module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverExtension
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowStandardAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowSourceUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.FiniteCompletionComplexHomExt
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal

/-!
# 元のκの各項と元の指定被覆同型の一致

## 概要
元の半自由完備行射の各項は、独立に構成した始域比較と元の指定剰余被覆同型を計算する。

## 方針
元の完備化単位上で元の模型増大と係数増大を照合し、完備な終域への射の一意性を使う。

## 規約
κの擬同型性で射の等式を置き換えず、元のaffineReducedCoverTermIsoを保持する。

## 使われ方
HT04.R1の指定された項ごとの法則。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal
open HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元のκの各項は、元の指定同型の後に同じ標準完備化単位を合成した射そのもの。 -/
theorem affineCoverResolvedRowsMap_point_law
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let Q := Construction61.crystallineCover P
    let hQ := Construction61.crystallineCover_bounded P
    let KQ := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj ((affineBaseModules Q hQ r).obj n)
    DerivedCategory.Q.map ((affineCoverResolvedRowsMap P hP r).app n) =
      (affineResolvedRowBoundedSourceIso P hP r n).hom ≫
      (affineReducedCoverTermIso P hP r n).hom ≫
      DerivedCategory.Q.map (finiteCompletionUnit (coverImageCoordinates P) KQ) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let f := Construction61.crystallineCoverMap P
  let α := f.toRingHom
  let M := (affineBaseModules P hP r).obj n
  let N := (affineBaseModules Q hQ r).obj n
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let KQ := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj N
  let L := baseChange α ((complexResolutionFunctor A).obj K)
  let y := coverImageCoordinates P
  let ε : (complexResolutionFunctor A).obj K ⟶ K := (complexResolutionAugmentation A).app K
  let g : L ⟶ KQ := ((ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)).map ε ≫
    (affineAnyExtendedSingleRowsMap f hP hQ r).app n
  let k := (affineCoverResolvedRowsMap P hP r).app n
  let t := affineResolvedRowUncompletedSourceIso P hP r n
  let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  let u := (derivedComplexCompletionUnit B (p : B)).app Y ≫
    (derivedComplexCompletionUnit B (p : B)).app ((derivedComplexCompletionFunctor B (p : B)).obj Y)
  let uN := DerivedCategory.Q.map (finiteCompletionUnit y KQ)
  let a := affineDerivedReducedCoefficientMap f hP hQ r n
  have hk := affineResolvedCompletedRowsMap_app f hP hQ r ![(p : A), P.generator] n
  simp only [resolvedCosimplicialAugmentation] at hk
  have hu : DerivedCategory.Q.map g ≫ uN =
      DerivedCategory.Q.map (finiteCompletionUnit y L) ≫ DerivedCategory.Q.map k := by
    dsimp only [k, affineCoverResolvedRowsMap]
    simp only [f, hQ] at hk
    rw [hk]
    simpa only [Functor.map_comp, g, k, y, L, K, KQ, ε, N, M, α, f, hQ, coefficientSingleRows, Functor.comp_obj] using congrArg DerivedCategory.Q.map
      (finiteCompletionUnit_naturality y g)
  have hs : DerivedCategory.Q.map (finiteCompletionUnit y L) ≫
      (affineResolvedRowBoundedSourceIso P hP r n).hom = t.hom ≫ u :=
    affineResolvedRowBoundedSourceIso_unit P hP r n
  have hr : u ≫ (affineReducedCoverTermIso P hP r n).hom = a :=
    affineReducedCoverTermIso_unit P hP r n
  have ha : t.hom ≫ a = DerivedCategory.Q.map g := affineResolvedRow_standardAugmentation P hP r n
  apply finiteCompletionComplexHom_ext y L
    (DerivedCategory.Q.obj ((finiteCompletionFunctor y).obj KQ))
    (fun j => finiteCompletion_isComplete y KQ j)
  calc
    _ = DerivedCategory.Q.map g ≫ uN := hu.symm
    _ = t.hom ≫ a ≫ uN := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ uN) ha.symm
    _ = t.hom ≫ u ≫ (affineReducedCoverTermIso P hP r n).hom ≫ uN := by
      simpa only [Category.assoc] using congrArg (fun q => t.hom ≫ q ≫ uN) hr.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ (affineReducedCoverTermIso P hP r n).hom ≫ uN) hs.symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
