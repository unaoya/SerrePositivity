module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientSections
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientBockstein
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZeroLeibniz
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechPrismBaseChange

/-!
# 元の係数変更と標準 Hodge–Tate 零次写像

## 概要
元の affine 係数変更が、元の構造切断・標準零次写像・その Bockstein を保つ。

## 方針
包の剰余への同一視と元の切断の可換式を、同じ余輪体の代表元で零次類へ移す。

## 規約
選択生成元を厳密に保つ場合に限る。単元倍の場合の Bockstein の係数は省略しない。

## 使われ方
特定の Zp 係数射の Tot 比較を、既存の標準 HT 写像へ接続する。
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
variable (r : ℕ) (hg : f.toRingHom P.generator = Q.generator) (n : SimplexCategory)
local notation "U" => affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl
local notation "V" => affineEnvelopeTerm Q hQ r n.len (cutoff B (affineAlgebra Q r)) le_rfl

include f
/-- 元の Cech 項そのものの型で読む、同じ包の係数 prism 射。 -/
def affineHTCoefficientPrismHom :
    OrientedPrism.Hom ((htCech P hP r).obj n).Q ((htCech Q hQ r).obj n).Q := by
  dsimp only [htCech, cechAlexanderAffine, cechAlexanderOfAffineTerms]
  exact affineEnvelopeCoefficientHom f U V

/-- 元の Cech 項の型で、同じ係数 prism 射は元の構造切断を保つ。 -/
theorem affineHTCoefficientPrismHom_sec :
    (affineHTCoefficientPrismHom f hP hQ r n).quotientMap.comp ((htCech P hP r).obj n).sec =
      ((htCech Q hQ r).obj n).sec.comp (affinePolynomialCoefficientMap f r) := by
  dsimp only [affineHTCoefficientPrismHom, htCech, cechAlexanderAffine,
    cechAlexanderOfAffineTerms]
  exact affineEnvelopeCoefficientHom_sec f U V

/-- 元の剰余表示の同型は、元の二つの係数射の正方形を保つ。 -/
theorem affineHTCoefficientResidue_square (x : (reducedModel P hP r).obj n) :
    htResidueIso Q hQ r n ((affineHTCoefficientReduced f hP hQ r hg).app n x) =
      (affineHTCoefficientPrismHom f hP hQ r n).quotientMap (htResidueIso P hP r n x) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 元の affine 係数変更は、元の完備多項式の構造切断を保つ。 -/
theorem affineHTCoefficientReduced_sec (x : affineAlgebra P r) :
    (affineHTCoefficientReduced f hP hQ r hg).app n (htSec P hP r n x) =
      htSec Q hQ r n (affinePolynomialCoefficientMap f r x) := by
  apply (htResidueIso Q hQ r n).injective
  rw [affineHTCoefficientResidue_square]
  change (affineHTCoefficientPrismHom f hP hQ r n).quotientMap
      ((htResidueIso P hP r n) ((htResidueIso P hP r n).symm
        (((htCech P hP r).obj n).sec x))) =
    (htResidueIso Q hQ r n)
      ((htResidueIso Q hQ r n).symm
        (((htCech Q hQ r).obj n).sec (affinePolynomialCoefficientMap f r x)))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun (affineHTCoefficientPrismHom_sec f hP hQ r n) x

/-- 元の係数変更は、元の標準 Hodge–Tate 零次写像を保つ。 -/
theorem affineHTCoefficient_hodgeTateMapZero (x : affineAlgebra P r) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) 0
      (hodgeTateMapZero P hP r x) =
        hodgeTateMapZero Q hQ r (affinePolynomialCoefficientMap f r x) := by
  change cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) 0
      (cohomologyClass (reducedModel P hP r) 0
        (zeroCocyclesEquiv _ (htSecZero P hP r x))) =
    cohomologyClass (reducedModel Q hQ r) 0
      (zeroCocyclesEquiv _ (htSecZero Q hQ r (affinePolynomialCoefficientMap f r x)))
  rw [cohomologyMap_class]
  apply congrArg (cohomologyClass (reducedModel Q hQ r) 0)
  apply Subtype.ext
  exact affineHTCoefficientReduced_sec f hP hQ r hg ⦋0⦌ x

/-- 元の係数変更は、元の零次 HT 類の Bockstein を保つ。 -/
theorem affineHTCoefficient_htBocksteinZero (x : affineAlgebra P r) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) 1
      (htBocksteinZero P hP r x) =
        htBocksteinZero Q hQ r (affinePolynomialCoefficientMap f r x) := by
  change cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) 1
      (bockstein P hP r 0 (hodgeTateMapZero P hP r x)) =
    bockstein Q hQ r 0 (hodgeTateMapZero Q hQ r (affinePolynomialCoefficientMap f r x))
  rw [affineHTCoefficientReduced_bockstein, affineHTCoefficient_hodgeTateMapZero]

end SerrePositivity.BhattScholze.Prismatic
