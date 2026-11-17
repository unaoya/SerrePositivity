module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryRowsCompletion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeAugmentationCanonicalIso

import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows

/-!
# 元のsingle行で模型を外した標準完備比較

## 概要
元の半自由行の増大を外した標準完備比較は、指定被覆の前提の下で同型。

## 方針
元の行のTor消滅で同じ増大の各項を検査し、一様下界でTotへ移して元の標準比較から外す。

## 規約
始域の選択生成元はpに制限しない。元のκと標準単位を使う。

## 使われ方
元のHT全複体の標準完備増大を検査し、ηの自然性の図式へ接続する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded DerivedCompletion HTComparisonTotal HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B)) (r : ℕ) {s : ℕ} (x : Fin s → A)
variable (hTor : ∀ n, scalarExtensionTorVanishing f.toRingHom ((affineBaseModules P hP r).obj n))
variable (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete B (f.toRingHom (x j))
  ((affineBaseModules Q hQ r).obj n))
include hg hTor hM

/-- 元の行のTor消滅と元の完備化単位から、同じ元の完備した行増大のTotは擬同型。 -/
theorem affineResolvedCompletedAugmentation_total_quasiIso :
    QuasiIso ((alternatingCofaceMapComplex (Complex B) ⋙
      cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
      (crystallineResolvedCompletedAugmentation f.toRingHom x
        (coefficientSingleRows (affineBaseModules P hP r)))) := by
  let X := coefficientSingleRows (affineBaseModules P hP r)
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let y := fun j => f.toRingHom (x j)
  have hrow (n : SimplexCategory) :
      QuasiIso ((crystallineResolvedCompletedAugmentation f.toRingHom x X).app n) := by
    haveI := baseChange_quasiIso_to_single_of_torVanishing f.toRingHom
      ((affineBaseModules P hP r).obj n) (hTor n)
      ((resolvedCosimplicialAugmentation X).app n)
      (resolvedCosimplicialAugmentation_quasiIso X n) (resolvedCosimplicial_kFlat X n)
    change QuasiIso ((finiteCompletionFunctor y).map
      (E.map ((resolvedCosimplicialAugmentation X).app n)))
    exact finiteCompletionFunctor_map_quasiIso y _
  have ht (n : ℕ) (i : ℤ) (hi : i < 0) :
      IsZero (((X ⋙ E ⋙ finiteCompletionFunctor y).obj (SimplexCategory.mk n)).homology i) := by
    let u := finiteCompletionUnit y (E.obj (X.obj (SimplexCategory.mk n)))
    haveI : QuasiIso u := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
      (finiteCompletionUnit_isIso_of_isComplete y _
        (fun j => affineOrdinaryRows_complete f hP hQ hg r x hM (SimplexCategory.mk n) j))
    exact (affineOrdinaryRows_lowerBound f hP hQ hg r n i hi).of_iso (isoOfQuasiIsoAt u i).symm
  exact total_map_quasiIso_of_rows _ 0
    (affineResolvedCompletedRows_lowerBound f hP hQ hg r x hTor hM) ht
    (fun n => hrow (SimplexCategory.mk n))

omit hg hTor hM
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 指定被覆の元のsingle行で、模型を選ばない標準完備比較自体が同型。 -/
theorem affineCoverCanonicalSingleComparison_isIso
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    IsIso (canonicalCompletedBaseChangeComparison (Construction61.crystallineCoverMap P).toRingHom
      ![(p : A), P.generator]
      ((alternatingCofaceMapComplex (Complex A)).obj (affineBaseSingleRows P hP r))) := by
  exact canonicalCosimplicialComparison_isIso_of_augmentation
    (Construction61.crystallineCoverMap P).toRingHom ![(p : A), P.generator]
    (affineBaseSingleRows P hP r) 0 (affineBaseSingleRows_lowerBound P hP r)
    (affineCover_completedTotalComparison_isIso P hP r hF hR)
    (affineResolvedCompletedAugmentation_total_quasiIso
      (Construction61.crystallineCoverMap P) hP (Construction61.crystallineCover_bounded P)
      (Construction61.crystallineCover_generator P) r ![(p : A), P.generator]
      (affineReducedCover_scalarExtensionTorVanishing P hP r) (affineCoverRows_complete P r))

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
