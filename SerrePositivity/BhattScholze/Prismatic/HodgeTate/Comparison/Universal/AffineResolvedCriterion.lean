module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineCriterion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineModelsComplete
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.ResolvedCoverReflection

/-!
# 元の affine line の射を被覆上で検出する判定

## 概要
元の基底へ制限した射の指定半自由分解の被覆像が擬同型なら、元の標準 HT 写像の加群比較が成立する。

## 方針
元の source・target の p・d 完備性を供給して反映を適用し、忠実な係数制限で元の射へ戻す。

## 規約
被覆像の擬同型性は明示した未解決の入力であり、この判定だけを HT 比較の証明とは数えない。
元の複体の K-flat 性を追加しない。

## 使われ方
Proposition 6.2 の被覆上の標準写像の計算と、元の affineLine_moduleComparison の型の接続。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion InfinityCategories HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-- 元の係数制限した射の被覆像の擬同型性から、元の標準 HT 加群比較へ戻る。 -/
theorem affineLine_moduleComparison_of_resolvedCover
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (h0 : (affineLineFormalZeroIso P).hom ≫ HomologicalComplex.homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (h1 : (affineLineFormalOneIso P).hom ≫ HomologicalComplex.homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1))
    (hf : QuasiIso ((Construction61.completedCoverModelFunctor P).map
      ((complexResolutionFunctor A).map
        (((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).mapHomologicalComplex
          (.up ℤ)).map η)))) :
    Function.Bijective (hodgeTateMapZero P hP 1) ∧ Function.Bijective (hodgeTateMapOne P hP 1) ∧
      ∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' P hP 1 i) := by
  let F := ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)
  have hr : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map η) :=
    quasiIso_of_resolvedCover_map_quasiIso P hF hR _
      (affineLineFormal_complete_p P) (affineHTTotal_complete_p P hP 1)
      (affineComplexOnBase_complete_generator P 1 _)
      (affineComplexOnBase_complete_generator P 1 _) hf
  haveI : QuasiIso η :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology η F).mp hr
  exact affineLine_moduleComparison_of_realization P hP η h0 h1

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
