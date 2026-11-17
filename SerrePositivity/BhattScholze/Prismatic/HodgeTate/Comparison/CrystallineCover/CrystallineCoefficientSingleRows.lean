module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeCosimplicialComparison
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# 結晶係数比較の元の離散行と半自由模型

## 概要
元の余単体的加群を零次の行へ置き、平坦な係数射について半自由増大の完備係数変更を比較する。

## 方針
既存の single と加群の係数拡大の自然同型、平坦な係数拡大の完全性を使う。

## 規約
半自由模型の各項の零性は要求しない。元の離散行の一様ホモロジー下界だけを使う。

## 使われ方
特定の Zp 係数射の標準の導来完備係数変更から、元の affine 剰余行への自然な比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open HTComparisonTotal HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の余単体的加群を、整数次数零に置いた同じ行図式。 -/
abbrev coefficientSingleRows (M : CosimplicialObject (ModuleCat.{u} R)) :
    CosimplicialObject (Complex R) :=
  M ⋙ HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0

/-- 元の離散行には、一様な零のホモロジー下界がある。 -/
theorem coefficientSingleRows_lowerBound (M : CosimplicialObject (ModuleCat.{u} R))
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero (((coefficientSingleRows M).obj ⦋n⦌).homology i) :=
  HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 (M.obj ⦋n⦌) i (by omega)

/-- 元の通常係数拡大は、零次の行への包含と自然に可換。 -/
def coefficientExtendedSingleRowsIso (f : R →+* S)
    (M : CosimplicialObject (ModuleCat.{u} R)) :
    coefficientSingleRows M ⋙ (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ≅
      coefficientSingleRows (M ⋙ ModuleCat.extendScalars f) :=
  Functor.isoWhiskerLeft M
    (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars f) (.up ℤ) 0)

/-- 同じ半自由増大を標準の完備係数拡大に通した自然変換。 -/
def crystallineResolvedCompletedAugmentation (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) :
    resolvedCompletedBaseChange f x X ⟶
      X ⋙ ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
        finiteCompletionFunctor (fun j => f (x j))) :=
  Functor.whiskerRight (resolvedCosimplicialAugmentation X)
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
      finiteCompletionFunctor (fun j => f (x j)))

/-- 平坦な係数射では、同じ完備係数拡大後の増大も各行で擬同型。 -/
theorem crystallineResolvedCompletedAugmentation_quasiIso (f : R →+* S) (hf : f.Flat)
    {r : ℕ} (x : Fin r → R) (X : CosimplicialObject (Complex R)) (n : SimplexCategory) :
    QuasiIso ((crystallineResolvedCompletedAugmentation f x X).app n) := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI := resolvedCosimplicialAugmentation_quasiIso X n
  haveI : QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
      ((resolvedCosimplicialAugmentation X).app n)) := by infer_instance
  exact finiteCompletionFunctor_map_quasiIso (fun j => f (x j)) _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
