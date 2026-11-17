module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCriterion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverOrdinaryComparison

/-!
# 同じ制限関手の型で読む元の被覆反映判定

## 概要
元の反映判定の入力を、同じ `affineRestrictedComplexFunctor` の射として読む。

## 方針
具体的な普遍基底へ特殊化する前に、制限関手の略記と元の射の型を照合する。

## 規約
射・完備被覆模型・反映の仮定・終点は変えない。

## 使われ方
HT04.R3 で、検証した同じηの完備被覆像を元の反映判定へ渡す。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の同じηと制限関手の型による、元の標準HT写像への反映判定。 -/
theorem affineLine_moduleComparison_of_restrictedResolvedCover
    (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (hF : IsCompletelyFlat (Ideal.span {Construction61.coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (h0 : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (h1 : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1))
    (hf : QuasiIso ((Construction61.completedCoverModelFunctor P).map
      ((complexResolutionFunctor A).map ((affineRestrictedComplexFunctor P 1).map η)))) :
    Function.Bijective (hodgeTateMapZero P hP 1) ∧
      Function.Bijective (hodgeTateMapOne P hP 1) ∧
      ∀ i : ℕ, 1 < i → Subsingleton (hodgeTateCohomology' P hP 1 i) := by
  exact affineLine_moduleComparison_of_resolvedCover P hP hF hR η h0 h1 hf

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
