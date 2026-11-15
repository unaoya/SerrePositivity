module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCompleteSingleRows

/-!
# 結晶係数での半自由完備行と元の完備な離散行の Tot

## 概要
平坦な係数拡大後の元の離散行が完備なら、同じ半自由完備行の Tot を元の離散行の Tot に戻す。

## 方針
元の半自由増大と single の自然同型で完備行へ写し、元の完備化単位の Tot の逆を導来圏で合成する。

## 規約
擬同型の逆鎖写像は選ばない。各頂点の一様下界はホモロジーの下界である。

## 使われ方
特定の Zp 係数射について、Lemma 4.22 の標準の完備導来底変換を元の affine 行へ戻す。
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
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の半自由増大と single の自然同型による、同じ完備行への指定射。 -/
def crystallineResolvedToCompletedSingleRows (f : R →+* S) (a : R)
    (M : CosimplicialObject (ModuleCat.{u} R)) :
    resolvedCompletedBaseChange f (fun _ : Fin 1 => a) (coefficientSingleRows M) ⟶
      coefficientSingleRows (M ⋙ ModuleCat.extendScalars f) ⋙
        finiteCompletionFunctor (fun _ : Fin 1 => f a) :=
  crystallineResolvedCompletedAugmentation f (fun _ : Fin 1 => a) (coefficientSingleRows M) ≫
    (Functor.isoWhiskerRight (coefficientExtendedSingleRowsIso f M)
      (finiteCompletionFunctor (fun _ : Fin 1 => f a))).hom

/-- 平坦な係数射の下で、この指定された各行の射は擬同型である。 -/
theorem crystallineResolvedToCompletedSingleRows_quasiIso (f : R →+* S) (hf : f.Flat)
    (a : R) (M : CosimplicialObject (ModuleCat.{u} R)) (n : SimplexCategory) :
    QuasiIso ((crystallineResolvedToCompletedSingleRows f a M).app n) := by
  haveI := crystallineResolvedCompletedAugmentation_quasiIso f hf
    (fun _ : Fin 1 => a) (coefficientSingleRows M) n
  change QuasiIso (((crystallineResolvedCompletedAugmentation f
    (fun _ : Fin 1 => a) (coefficientSingleRows M)).app n) ≫ _)
  infer_instance

/-- 元の拡大行の完備性から、半自由完備行の同じ一様な零の下界を得る。 -/
theorem crystallineResolvedSingleRows_lowerBound (f : R →+* S) (hf : f.Flat)
    (a : R) (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory,
      IsModuleComplete S (f a) ((ModuleCat.extendScalars f).obj (M.obj n)))
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero (((resolvedCompletedBaseChange f (fun _ : Fin 1 => a)
      (coefficientSingleRows M)).obj ⦋n⦌).homology i) := by
  haveI := crystallineResolvedToCompletedSingleRows_quasiIso f hf a M ⦋n⦌
  exact (coefficientCompletedSingleRows_lowerBound (f a)
    (M ⋙ ModuleCat.extendScalars f) hM n i hi).of_iso
      (isoOfQuasiIsoAt ((crystallineResolvedToCompletedSingleRows f a M).app ⦋n⦌) i)

/-- 指定された各行の比較は、元の積 Tot でも擬同型である。 -/
theorem crystallineResolvedToCompletedSingleRows_total_quasiIso
    (f : R →+* S) (hf : f.Flat) (a : R) (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory,
      IsModuleComplete S (f a) ((ModuleCat.extendScalars f).obj (M.obj n))) :
    QuasiIso ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
      ((alternatingCofaceMapComplex (Complex S)).map
        (crystallineResolvedToCompletedSingleRows f a M))) :=
  total_map_quasiIso_of_rows _ 0 (crystallineResolvedSingleRows_lowerBound f hf a M hM)
    (coefficientCompletedSingleRows_lowerBound (f a) (M ⋙ ModuleCat.extendScalars f) hM)
    (fun n => crystallineResolvedToCompletedSingleRows_quasiIso f hf a M ⦋n⦌)

/-- 同じ自然な増大と標準単位だけからなる、元の離散行の Tot への導来同型。 -/
def crystallineResolvedOrdinaryTotalIso (f : R →+* S) (hf : f.Flat)
    (a : R) (M : CosimplicialObject (ModuleCat.{u} R))
    (hM : ∀ n : SimplexCategory,
      IsModuleComplete S (f a) ((ModuleCat.extendScalars f).obj (M.obj n))) :
    DerivedCategory.Q.obj (cosimplicialTotal
        (resolvedCompletedBaseChange f (fun _ : Fin 1 => a) (coefficientSingleRows M))) ≅
      DerivedCategory.Q.obj (cosimplicialTotal
        (coefficientSingleRows (M ⋙ ModuleCat.extendScalars f))) := by
  haveI := crystallineResolvedToCompletedSingleRows_total_quasiIso f hf a M hM
  haveI := coefficientSingleCompletionUnit_total_quasiIso (f a)
    (M ⋙ ModuleCat.extendScalars f) hM
  exact asIso (DerivedCategory.Q.map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
        ((alternatingCofaceMapComplex (Complex S)).map
          (crystallineResolvedToCompletedSingleRows f a M)))) ≪≫
    (asIso (DerivedCategory.Q.map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
        ((alternatingCofaceMapComplex (Complex S)).map
          (coefficientSingleCompletionUnit (f a) (M ⋙ ModuleCat.extendScalars f)))))).symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
