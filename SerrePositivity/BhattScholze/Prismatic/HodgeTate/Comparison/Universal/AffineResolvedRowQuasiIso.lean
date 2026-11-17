module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedOrdinaryRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.TorAcyclicResolvedRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.FiniteCompleteSingleRows

/-!
# 元の向き付き行のTor非輪状な係数変更とTot

## 概要
元の行の高次Torが消え、終域が指定座標で完備なら、同じ標準完備行射とTotは擬同型となる。

## 方針
元のK-flat増大の係数拡大、元の通常係数射、元の有限完備化単位を順に使う。

## 規約
任意の非有界複体の平坦性を要求しない。行のTor消滅と終域の完備性は適用側で与える。

## 使われ方
具体的な被覆の定義を展開せず、同じ厳密な行比較を元の積Totへ接続する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HomologicalAlgebra HTComparisonTotal HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B)) (r : ℕ) {s : ℕ} (x : Fin s → A)
variable (hTor : ∀ n, scalarExtensionTorVanishing f.toRingHom ((affineBaseModules P hP r).obj n))

include hg hTor
/-- 元の標準完備行射は、元の行のTor消滅の下で各行ごとに擬同型。 -/
theorem affineResolvedCompletedRowsMap_quasiIso (n : SimplexCategory) :
    QuasiIso ((affineResolvedCompletedRowsMap f hP hQ r x).app n) := by
  let X := coefficientSingleRows (affineBaseModules P hP r)
  haveI := baseChange_quasiIso_to_single_of_torVanishing f.toRingHom
    ((affineBaseModules P hP r).obj n) (hTor n)
    ((resolvedCosimplicialAugmentation X).app n)
    (resolvedCosimplicialAugmentation_quasiIso X n) (resolvedCosimplicial_kFlat X n)
  haveI := affineAnyExtendedSingleRowsMap_app_isIso f hP hQ hg r n
  rw [affineResolvedCompletedRowsMap_app]
  exact finiteCompletionFunctor_map_quasiIso _ _

variable (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete B (f.toRingHom (x j))
  ((affineBaseModules Q hQ r).obj n))
include hg hTor hM
/-- 同じ元の完備行のホモロジーは、元の終域と同じ零の一様下界を持つ。 -/
theorem affineResolvedCompletedRows_lowerBound (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero (((resolvedCompletedBaseChange f.toRingHom x
      (coefficientSingleRows (affineBaseModules P hP r))).obj ⦋n⦌).homology i) := by
  haveI := affineResolvedCompletedRowsMap_quasiIso f hP hQ hg r x hTor ⦋n⦌
  exact (coefficientFiniteCompletedSingleRows_lowerBound (fun j => f.toRingHom (x j))
    (affineBaseModules Q hQ r) hM n i hi).of_iso
      (isoOfQuasiIsoAt ((affineResolvedCompletedRowsMap f hP hQ r x).app ⦋n⦌) i)

/-- 元の標準完備行射の同じ積Totも、元の一様下界により擬同型。 -/
theorem affineResolvedCompletedRows_total_quasiIso :
    QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
      ((alternatingCofaceMapComplex (Complex B)).map (affineResolvedCompletedRowsMap f hP hQ r x))) :=
  total_map_quasiIso_of_rows _ 0 (affineResolvedCompletedRows_lowerBound f hP hQ hg r x hTor hM)
    (coefficientFiniteCompletedSingleRows_lowerBound (fun j => f.toRingHom (x j))
      (affineBaseModules Q hQ r) hM)
    (fun n => affineResolvedCompletedRowsMap_quasiIso f hP hQ hg r x hTor ⦋n⦌)

/-- 元の標準完備行射と元の完備化単位により、元の終域のTotへ戻る指定同型。 -/
def affineResolvedCompletedTotalIso :
    DerivedCategory.Q.obj (cosimplicialTotal (resolvedCompletedBaseChange f.toRingHom x
      (coefficientSingleRows (affineBaseModules P hP r)))) ≅
      DerivedCategory.Q.obj (cosimplicialTotal (coefficientSingleRows (affineBaseModules Q hQ r))) := by
  let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
  haveI := affineResolvedCompletedRows_total_quasiIso f hP hQ hg r x hTor hM
  haveI := coefficientSingleFiniteCompletionUnit_total_quasiIso
    (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r) hM
  haveI : IsIso (DerivedCategory.Q.map (T.map (affineResolvedCompletedRowsMap f hP hQ r x))) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} B) _).mpr
    exact affineResolvedCompletedRows_total_quasiIso f hP hQ hg r x hTor hM
  haveI : IsIso (DerivedCategory.Q.map (T.map (coefficientSingleFiniteCompletionUnit
      (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r)))) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} B) _).mpr
    exact coefficientSingleFiniteCompletionUnit_total_quasiIso
      (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r) hM
  exact asIso (DerivedCategory.Q.map (T.map (affineResolvedCompletedRowsMap f hP hQ r x))) ≪≫
    (asIso (DerivedCategory.Q.map (T.map (coefficientSingleFiniteCompletionUnit
      (fun j => f.toRingHom (x j)) (affineBaseModules Q hQ r))))).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
