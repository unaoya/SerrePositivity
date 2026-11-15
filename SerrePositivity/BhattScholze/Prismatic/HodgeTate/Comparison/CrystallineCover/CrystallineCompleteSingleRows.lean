module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionIdempotent

/-!
# 完備な元の離散行への標準完備化単位

## 概要
元の完備な余単体的加群を零次へ置くと、元の p 完備化単位は各行と Tot で擬同型になる。

## 方針
加群の元の導来完備性を同じ single 複体に読み替え、元の標準単位を使う。

## 規約
単位の逆鎖写像は選ばない。導来圏での同型と自然な擬同型の列を使う。

## 使われ方
特定の Zp 係数射による元の離散行と、半自由模型の完備行をつなぐ。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- 元の single 行から、同じ行の標準主元完備化への自然な単位。 -/
def coefficientSingleCompletionUnit (M : CosimplicialObject (ModuleCat.{u} R)) :
    coefficientSingleRows M ⟶
      coefficientSingleRows M ⋙ finiteCompletionFunctor (fun _ : Fin 1 => a) where
  app n := finiteCompletionUnit (fun _ : Fin 1 => a) ((coefficientSingleRows M).obj n)
  naturality _ _ g := finiteCompletionUnit_naturality _ ((coefficientSingleRows M).map g)

/-- 元の加群が完備なら、同じ single 行の標準完備化単位は擬同型。 -/
theorem coefficientSingleCompletionUnit_quasiIso
    (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory, IsModuleComplete R a (M.obj n)) (n : SimplexCategory) :
    QuasiIso ((coefficientSingleCompletionUnit a M).app n) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).mp
  apply finiteCompletionUnit_isIso_of_isComplete
  intro j
  change IsComplete R a ((moduleObjectFunctor R).obj (M.obj n))
  exact hM n

/-- 元の完備行と、その標準完備化後の同じ行は一様な零の下界を共有する。 -/
theorem coefficientCompletedSingleRows_lowerBound
    (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory, IsModuleComplete R a (M.obj n))
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero (((coefficientSingleRows M ⋙
      finiteCompletionFunctor (fun _ : Fin 1 => a)).obj ⦋n⦌).homology i) := by
  haveI := coefficientSingleCompletionUnit_quasiIso a M hM ⦋n⦌
  exact (coefficientSingleRows_lowerBound M n i hi).of_iso
    (isoOfQuasiIsoAt ((coefficientSingleCompletionUnit a M).app ⦋n⦌) i).symm

/-- 元の完備な single 行の標準完備化単位は、指定された積 Tot でも擬同型。 -/
theorem coefficientSingleCompletionUnit_total_quasiIso
    (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory, IsModuleComplete R a (M.obj n)) :
    QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      ((alternatingCofaceMapComplex (Complex R)).map (coefficientSingleCompletionUnit a M))) :=
  total_map_quasiIso_of_rows _ 0 (coefficientSingleRows_lowerBound M)
    (coefficientCompletedSingleRows_lowerBound a M hM)
    (fun n => coefficientSingleCompletionUnit_quasiIso a M hM ⦋n⦌)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
