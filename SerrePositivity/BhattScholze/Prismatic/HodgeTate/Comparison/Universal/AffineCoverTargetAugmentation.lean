module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCanonicalSingleRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryRowsCompletion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.SingleRowsOrdinaryTotal
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedAugmentationFromTotal
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ResolvedOrdinaryCompleteAugmentation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverOrdinaryComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalTotalModel

import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverOrdinaryComparison

/-!
# 元のHT全複体の指定被覆への完備した標準増大

## 概要
元のHT全複体で、指定半自由増大の完備した被覆像が擬同型となる。

## 方針
元のsingle行の標準比較から増大を取り出し、元の全複体の同型と座標の同伴性で運ぶ。

## 規約
元の増大そのものの擬同型性を証明する。対象の同型の存在で置き換えない。

## 使われ方
元のηの被覆像を、同じ通常係数拡大の射へ自然に比較する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded DerivedCompletion HTComparisonTotal HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元のsingle行のTotへの通常被覆係数拡大は、元の像の座標で完備。 -/
theorem affineCoverOrdinarySingleTotal_complete (j : Fin 2) :
    IsComplete (Construction61.crystallineCoverRing P) (coverImageCoordinates P j)
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
          (.up ℤ)).obj (cosimplicialTotal (affineBaseSingleRows P hP r)))) := by
  let B := Construction61.crystallineCoverRing P
  let E := (ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ)
  let e := DerivedCategory.Q.mapIso (E.mapIso (affineBaseSingleTotalPolynomialIso P hP r))
  have hc : IsComplete B (coverImageCoordinates P j)
      (DerivedCategory.Q.obj (E.obj (affineComplexOnBase P r (affineHTTotalComplex P hP r)))) :=
    (isComplete_associated_iff _ _ (coverImageCoordinates_associated P j) _).mpr
      (affineCoverBaseChange_complete_p P r (affineHTTotalComplex P hP r))
  exact isComplete_of_iso B _ e.symm hc

variable
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
include hF hR

/-- 元のHT全複体の指定半自由増大は、元の完備した被覆係数拡大で擬同型。 -/
theorem affineHTTotal_completedCoverAugmentation_quasiIso :
    QuasiIso ((Construction61.completedCoverModelFunctor P).map
      ((complexResolutionAugmentation A).app
        (affineComplexOnBase P r (affineHTTotalComplex P hP r)))) := by
  let B := Construction61.crystallineCoverRing P
  let Q := Construction61.crystallineCover P
  let hQ := Construction61.crystallineCover_bounded P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let X := affineBaseSingleRows P hP r
  let K := (alternatingCofaceMapComplex (Complex A)).obj X
  let q := (complexResolutionAugmentation A).app (total K)
  haveI := affineCoverCanonicalSingleComparison_isIso P hP r hF hR
  haveI : IsIso (baseChangeTotalComparison α K) := by
    apply baseChangeTotalComparison_isIso_of_singleRows
    intro n j hj
    change IsZero (((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      ((affineBaseModules P hP r).obj ⦋n⦌)).X j)
    exact isZero_single_obj_X (.up ℤ) 0 _ j hj
  haveI := affineOrdinaryRowsCompletionUnit_total_quasiIso (Construction61.crystallineCoverMap P)
    hP hQ (Construction61.crystallineCover_generator P) r ![(p : A), P.generator]
    (affineCoverRows_complete P r)
  have hq := completedAugmentation_quasiIso_of_totalComparison α ![(p : A), P.generator]
    K q (complexResolutionAugmentation_quasiIso A _) (complexResolutionFunctor_kFlat A _)
    (affineCoverOrdinarySingleTotal_complete P hP r)
  have ht := completedResolutionAugmentation_quasiIso_of_iso α (coverImageCoordinates P)
    (affineBaseSingleTotalPolynomialIso P hP r).symm hq
  exact (coverImageCompletion_quasiIso_iff P _).mp ht

/-- 元のHT全複体でも、元の指定増大と元の標準単位の比較成分が同型となる。 -/
theorem affineHTTotalCoverOrdinaryComparison_isIso :
    IsIso ((affineCoverOrdinaryComparison P r).app (affineHTTotalComplex P hP r)) :=
  resolvedOrdinaryComparison_app_isIso_of_completed (Construction61.crystallineCoverMap P).toRingHom
    (fun _ : Fin 2 => (p : Construction61.crystallineCoverRing P))
    (affineRestrictedComplexFunctor P r) (fun K _ => affineCoverBaseChange_complete_p P r K)
    (affineHTTotalComplex P hP r) (affineHTTotal_completedCoverAugmentation_quasiIso P hP r hF hR)

/-- 元のηの通常被覆像が擬同型なら、元の指定分解の完備被覆像も擬同型。 -/
theorem affineLine_resolvedCover_quasiIso_of_ordinary
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (hη : QuasiIso ((affineOrdinaryCoverFunctor P 1).map η)) :
    QuasiIso ((Construction61.completedCoverModelFunctor P).map
      ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η))) := by
  have hηQ : IsIso ((affineOrdinaryCoverFunctor P 1 ⋙ DerivedCategory.Q).map η) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hη
  letI := hηQ
  haveI := affineLineFormalCoverOrdinaryComparison_isIso P hP
  haveI := affineHTTotalCoverOrdinaryComparison_isIso P hP 1 hF hR
  have hn := (affineCoverOrdinaryComparison P 1).naturality η
  haveI : IsIso ((affineResolvedCoverFunctor P 1 ⋙ DerivedCategory.Q).map η ≫
      (affineCoverOrdinaryComparison P 1).app (affineHTTotalComplex P hP 1)) := by
    rw [hn]
    infer_instance
  have hηRes : IsIso ((affineResolvedCoverFunctor P 1 ⋙ DerivedCategory.Q).map η) :=
    IsIso.of_isIso_comp_right _
      ((affineCoverOrdinaryComparison P 1).app (affineHTTotalComplex P hP 1))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hηRes

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
