module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCompleteSingleRows

/-!
# 元の離散行の有限座標完備化の標準単位とTot

## 概要
元の各行が指定した有限座標で導来完備なら、同じ行と同じ積Totの完備化単位は擬同型となる。

## 方針
元の有限合成単位の普遍性と、元の離散行の零の一様下界を使う。

## 規約
各行の導来完備性を明示する。任意に選んだ行同型を図式へ持ち上げない。

## 使われ方
被覆の像の二座標で完備化した終域の行を、元の被覆上の剰余行へ戻す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HomologicalAlgebra HTComparisonTotal HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {s : ℕ} (x : Fin s → R)

/-- 元のsingle行から同じ有限反復完備行への標準合成単位。 -/
def coefficientSingleFiniteCompletionUnit (M : CosimplicialObject (ModuleCat.{u} R)) :
    coefficientSingleRows M ⟶ coefficientSingleRows M ⋙ finiteCompletionFunctor x where
  app n := finiteCompletionUnit x ((coefficientSingleRows M).obj n)
  naturality _ _ θ := finiteCompletionUnit_naturality x ((coefficientSingleRows M).map θ)

/-- 元の行が全指定座標で完備なら、その元の合成単位は擬同型。 -/
theorem coefficientSingleFiniteCompletionUnit_quasiIso
    (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete R (x j) (M.obj n)) (n : SimplexCategory) :
    QuasiIso ((coefficientSingleFiniteCompletionUnit x M).app n) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mp
  apply finiteCompletionUnit_isIso_of_isComplete
  intro j
  change IsComplete R (x j) ((moduleObjectFunctor R).obj (M.obj n))
  exact hM n j

/-- 元の完備行の有限反復完備化後も、同じ零の一様なホモロジー下界を持つ。 -/
theorem coefficientFiniteCompletedSingleRows_lowerBound
    (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete R (x j) (M.obj n))
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero (((coefficientSingleRows M ⋙ finiteCompletionFunctor x).obj ⦋n⦌).homology i) := by
  haveI := coefficientSingleFiniteCompletionUnit_quasiIso x M hM ⦋n⦌
  exact (coefficientSingleRows_lowerBound M n i hi).of_iso
    (isoOfQuasiIsoAt ((coefficientSingleFiniteCompletionUnit x M).app ⦋n⦌) i).symm

/-- 同じ元の合成単位は、元の積Totでも擬同型。 -/
theorem coefficientSingleFiniteCompletionUnit_total_quasiIso
    (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory, ∀ j, IsModuleComplete R (x j) (M.obj n)) :
    QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      ((alternatingCofaceMapComplex (Complex R)).map (coefficientSingleFiniteCompletionUnit x M))) :=
  total_map_quasiIso_of_rows _ 0 (coefficientSingleRows_lowerBound M)
    (coefficientFiniteCompletedSingleRows_lowerBound x M hM)
    (fun n => coefficientSingleFiniteCompletionUnit_quasiIso x M hM ⦋n⦌)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
