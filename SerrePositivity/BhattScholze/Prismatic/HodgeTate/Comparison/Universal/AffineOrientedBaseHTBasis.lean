module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineBasePolynomialCohomologyClasses
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedRawBasis
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineNativeBaseHodgeTate
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseHodgeTateMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords

/-!
# 元の基底係数HT写像の向き付き基底の値

## 概要
元のHT写像を基底係数で読み、単項式・外積基底の係数変更を零次・一次で照合する。

## 方針
同じ元のコホモロジー類を保持し、一次にはBocksteinの元の向きの単位の逆を残す。

## 規約
始域の生成元をpに制限しない。一次の向きの単位を消さない。

## 使われ方
元のηの通常被覆像の正方形を、元の標準HT写像との等式へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.DeRham SerrePositivity.Cosimplicial HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r i : ℕ)

/-- 元の基底係数HT写像の完備化単位での値は、元の同じHT類である。 -/
theorem affineBaseHTMap_completedFormsUnit (w : forms (A ⧸ P.ideal) (formVars.{u} r) i) :
    affineBaseHTMap P hP r i (completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p i w) =
      affineNativeBaseCohomologyEquiv P hP r i (affineHTRawMap P hP r i w) := by
  change (affineBasePolynomialCohomologyIso P hP r i).hom
    (affineHTCohomologyEquiv P hP r i (affineHTRawMap P hP r i w)) = _
  exact affineBasePolynomialCohomologyIso_cohomology P hP r i _

variable {P} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q) (hQ : IsBoundedPrism Q)

/-- 零次の元の基底全体で、同じ元の係数射は元の標準HT写像を保つ。 -/
theorem affineAnyBaseHTMap_basis_zero
    (w : (formVars.{u} r →₀ ℕ) × Set.powersetCard (formVars.{u} r) 0) :
    affineNativeBaseCohomologyEquiv Q hQ r 0
        (cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 0
          (affineHTRawMap P hP r 0 (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) 0 w))) =
      affineBaseHTMap Q hQ r 0 (completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p 0
        (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) 0 w)) := by
  rw [affineHTRawMap_basis_zero_any, affineBaseHTMap_completedFormsUnit]

/-- 一次の元の基底全体で、同じ元の係数射は向きの単位の逆を係数に持つ。 -/
theorem affineAnyBaseHTMap_basis_one (v : Bˣ)
    (hv : f.toRingHom P.generator = Q.generator * (v : B))
    (w : (formVars.{u} r →₀ ℕ) × Set.powersetCard (formVars.{u} r) 1) :
    affineNativeBaseCohomologyEquiv Q hQ r 1
        (cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 1
          (affineHTRawMap P hP r 1 (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) 1 w))) =
      ((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ r 1
        (completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p 1
          (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) 1 w)) := by
  letI := htModule Q hQ r 1
  have h := congrArg (affineNativeBaseCohomologyEquiv Q hQ r 1)
    (affineHTRawMap_basis_one_unit f hP hQ r v hv w)
  rw [affineNativeBaseCohomologyEquiv_smul] at h
  rw [affineBaseHTMap_completedFormsUnit, h, smul_smul]
  simp only [Units.inv_mul, one_smul]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
