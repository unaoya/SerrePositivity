module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedOrdinaryRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompleteTotalUnit

/-!
# 元の通常係数拡大した行の完備性と標準単位

## 概要
元の通常行射の同型により、同じ通常係数拡大した行は指定座標で完備となる。

## 方針
終域の元のsingle行の完備性と一様下界を、元の同じ通常行射で戻す。

## 規約
始域の生成元をpとせず、元の標準有限完備化単位のTotを使う。

## 使われ方
元のHT全複体で、標準完備比較を完備した増大へ分解する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HomologicalAlgebra DifferentialGraded DerivedCompletion HTComparisonTotal HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B)) (r : ℕ) {s : ℕ} (x : Fin s → A)
variable (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete B (f.toRingHom (x j))
  ((affineBaseModules Q hQ r).obj n))
include hg hM

/-- 元の通常係数拡大した各行は、元の終域と同じ指定座標で導来完備。 -/
theorem affineOrdinaryRows_complete (n : SimplexCategory) (j : Fin s) :
    IsComplete B (f.toRingHom (x j)) (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientSingleRows (affineBaseModules P hP r)).obj n))) := by
  haveI := affineAnyExtendedSingleRowsMap_app_isIso f hP hQ hg r n
  let e := DerivedCategory.Q.mapIso (asIso ((affineAnyExtendedSingleRowsMap f hP hQ r).app n))
  have hc : IsComplete B (f.toRingHom (x j))
      (DerivedCategory.Q.obj ((coefficientSingleRows (affineBaseModules Q hQ r)).obj n)) := hM n j
  exact isComplete_of_iso B _ e.symm hc

omit hM
include hg hQ
/-- 元の通常係数拡大した行は、元の終域と同じ一様な零の下界を持つ。 -/
theorem affineOrdinaryRows_lowerBound (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientSingleRows (affineBaseModules P hP r)).obj ⦋n⦌)).homology i) := by
  haveI := affineAnyExtendedSingleRowsMap_app_isIso f hP hQ hg r ⦋n⦌
  exact (coefficientSingleRows_lowerBound (affineBaseModules Q hQ r) n i hi).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) i).mapIso
      (asIso ((affineAnyExtendedSingleRowsMap f hP hQ r).app ⦋n⦌)))

include hM
/-- 同じ通常係数拡大した行の元の完備化単位は、同じ積Totでも擬同型。 -/
theorem affineOrdinaryRowsCompletionUnit_total_quasiIso :
    QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
      (finiteCompletionRowsUnit (fun j => f.toRingHom (x j))
        ((baseChangeRowsFunctor f.toRingHom).obj
          ((alternatingCofaceMapComplex (Complex A)).obj
            (coefficientSingleRows (affineBaseModules P hP r)))))) := by
  exact finiteCompletionRowsUnit_total_quasiIso_of_complete _ _ 0
    (affineOrdinaryRows_lowerBound f hP hQ hg r)
    (fun n j => affineOrdinaryRows_complete f hP hQ hg r x hM ⦋n⦌ j)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
