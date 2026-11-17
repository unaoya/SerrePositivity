module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientStandardZero
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule

/-!
# 元の affine 係数変更とコホモロジーの係数作用

## 概要
元の係数変更が、元の完備多項式係数の作用について半線形であることを示す。

## 方針
元の作用を標準零次 HT 類との cup 積で読み、標準零次写像と cup 積の自然性を使う。

## 規約
作用もコホモロジー写像も元のものを使う。選択生成元を厳密に保つ射に限る。

## 使われ方
特定の Zp 係数射のコホモロジー比較を、既存の標準 HT 写像の係数作用へ渡す。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.Cosimplicial
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (r : ℕ) (hg : f.toRingHom P.generator = Q.generator)

private theorem affineCoefficient_cohomologyMap_cast {i j : ℕ} (h : i = j)
    (x : hodgeTateCohomology' P hP r i) :
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) j
        (cast (congrArg (hodgeTateCohomology' P hP r) h) x) =
      cast (congrArg (hodgeTateCohomology' Q hQ r) h)
        (cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i x) := by
  subst j
  rfl

/-- 元のコホモロジーの係数変更は、元の affine 係数作用について半線形。 -/
theorem affineHTCoefficientCohomology_smul (i : ℕ) (a : affineAlgebra P r)
    (z : hodgeTateCohomology' P hP r i) :
    letI := htModule P hP r i
    letI := htModule Q hQ r i
    cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i (a • z) =
      affinePolynomialCoefficientMap f r a •
        cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i z := by
  letI := htModule P hP r i
  letI := htModule Q hQ r i
  rw [(htModuleData P hP r i).property a z,
    (htModuleData Q hQ r i).property (affinePolynomialCoefficientMap f r a)
      (cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i z)]
  rw [affineCoefficient_cohomologyMap_cast, cohomologyMap_cup,
    affineHTCoefficient_hodgeTateMapZero]
  omega

/-- 元のコホモロジー写像を、同じ係数作用に関する半線形写像として読む。 -/
def affineHTCoefficientCohomologyMap (i : ℕ) :
    letI := htModule P hP r i
    letI := htModule Q hQ r i
    hodgeTateCohomology' P hP r i →ₛₗ[affinePolynomialCoefficientMap f r]
      hodgeTateCohomology' Q hQ r i := by
  letI := htModule P hP r i
  letI := htModule Q hQ r i
  exact { __ := cohomologyMap _ _ (affineHTCoefficientReduced f hP hQ r hg) i
          map_smul' := affineHTCoefficientCohomology_smul f hP hQ r hg i }

end SerrePositivity.BhattScholze.Prismatic
