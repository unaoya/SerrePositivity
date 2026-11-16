module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientStandardZero
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineUnitBockstein
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientStandardZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero

/-!
# 向きの単位を残した標準零次・一次 HT 類の自然性

## 概要
生成元を単位倍で移す係数射について、元の切断と標準零次写像を比較する。

## 方針
元の包の剰余正方形を使い、一次には既存の単位付き Bockstein の式を適用する。

## 規約
一次の式の係数を省略しない。target の一次類は係数像の単位倍となる。

## 使われ方
Construction 6.1 の被覆で元の標準 η の値を照合する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
open SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (r : ℕ) (n : SimplexCategory)

/-- 元の剰余表示の同型は、元の二つの係数射の正方形を保つ。 -/
theorem affineHTCoefficientResidueAny_square (x : (reducedModel P hP r).obj n) :
    htResidueIso Q hQ r n ((affineHTCoefficientReducedAny f hP hQ r).app n x) =
      (affineHTCoefficientPrismHom f hP hQ r n).quotientMap (htResidueIso P hP r n x) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 元の affine 係数変更は、元の完備多項式の構造切断を保つ。 -/
theorem affineHTCoefficientReducedAny_sec (x : affineAlgebra P r) :
    (affineHTCoefficientReducedAny f hP hQ r).app n (htSec P hP r n x) =
      htSec Q hQ r n (affinePolynomialCoefficientMap f r x) := by
  apply (htResidueIso Q hQ r n).injective
  rw [affineHTCoefficientResidueAny_square]
  change (affineHTCoefficientPrismHom f hP hQ r n).quotientMap
      ((htResidueIso P hP r n) ((htResidueIso P hP r n).symm
        (((htCech P hP r).obj n).sec x))) =
    (htResidueIso Q hQ r n)
      ((htResidueIso Q hQ r n).symm
        (((htCech Q hQ r).obj n).sec (affinePolynomialCoefficientMap f r x)))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun (affineHTCoefficientPrismHom_sec f hP hQ r n) x

/-- 元の係数変更は、元の標準 Hodge–Tate 零次写像を保つ。 -/
theorem affineHTCoefficientAny_hodgeTateMapZero (x : affineAlgebra P r) :
    cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 0
      (hodgeTateMapZero P hP r x) =
        hodgeTateMapZero Q hQ r (affinePolynomialCoefficientMap f r x) := by
  change cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 0
      (cohomologyClass (reducedModel P hP r) 0
        (zeroCocyclesEquiv _ (htSecZero P hP r x))) =
    cohomologyClass (reducedModel Q hQ r) 0
      (zeroCocyclesEquiv _ (htSecZero Q hQ r (affinePolynomialCoefficientMap f r x)))
  rw [cohomologyMap_class]
  apply congrArg (cohomologyClass (reducedModel Q hQ r) 0)
  apply Subtype.ext
  exact affineHTCoefficientReducedAny_sec f hP hQ r ⦋0⦌ x

/-- 元の一次の標準 Bockstein 類は、選択生成元の単位に従って変換する。 -/
theorem affineHTCoefficientAny_htBocksteinZero_unit (u : Bˣ)
    (hu : f.toRingHom P.generator = Q.generator * (u : B)) (x : affineAlgebra P r) :
    letI := htModule Q hQ r 1
    htBocksteinZero Q hQ r (affinePolynomialCoefficientMap f r x) =
      affineBaseToPolynomialMap Q r (u : B) •
        cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 1
          (htBocksteinZero P hP r x) := by
  letI := htModule Q hQ r 1
  change bockstein Q hQ r 0 (hodgeTateMapZero Q hQ r (affinePolynomialCoefficientMap f r x)) =
    affineBaseToPolynomialMap Q r (u : B) •
      cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) 1
        (bockstein P hP r 0 (hodgeTateMapZero P hP r x))
  rw [← affineHTCoefficientAny_hodgeTateMapZero f hP hQ r]
  exact affineHTCoefficientReducedAny_bockstein_unit f hP hQ r u hu 0 _

end SerrePositivity.BhattScholze.Prismatic
