module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffinePolynomialCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative

/-!
# 元の通常形式の係数射と affine 係数変更

## 概要
元の変数改名と完備化単位から作る係数射が、元の prism 係数変更と可換であることを示す。

## 方針
多項式環の定数と変数で照合する。

## 規約
通常形式の変数は元の係数環と同じ宇宙に持ち上げる。

## 使われ方
元の標準 HT 写像の零次成分と座標一次成分の係数自然性。
-/

public noncomputable section
universe u
open SerrePositivity.DeRham
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (r : ℕ)

/-- 元の通常形式の係数を、元の affine 完備多項式係数へ送る構造射。 -/
def affineRawPolynomialCoefficient :
    Poly (A ⧸ P.ideal) (formVars.{u} r) →+* affineAlgebra P r :=
  (affineCoordinateIso P r).symm.toRingHom.comp
    (algebraMap (Poly (A ⧸ P.ideal) (formVars.{u} r))
      (completedPoly (A ⧸ P.ideal) (formVars.{u} r) p))

/-- 通常の定数は、元の affine 多項式の定数単位へ移る。 -/
theorem affineRawPolynomialCoefficient_C (c : A ⧸ P.ideal) :
    affineRawPolynomialCoefficient P r (MvPolynomial.C c) =
      prismPolynomialUnit P (Fin r) (MvPolynomial.C c) := by
  have h := coord_symm_map_C P r c
  have ht := (IsScalarTower.algebraMap_apply (A ⧸ P.ideal)
    (Poly (A ⧸ P.ideal) (formVars.{u} r))
    (completedPoly (A ⧸ P.ideal) (formVars.{u} r) p) c).symm
  rw [← ht] at h
  simpa only [e, affineRawPolynomialCoefficient, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    prismPolynomialAlgebra, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq] using h

/-- 持ち上げた変数は、元の有限変数の単位へ移る。 -/
theorem affineRawPolynomialCoefficient_X (t : formVars.{u} r) :
    affineRawPolynomialCoefficient P r (MvPolynomial.X t) =
      prismPolynomialUnit P (Fin r) (MvPolynomial.X t.down) := by
  apply (affineCoordinateIso P r).injective
  change affineCoordinateIso P r ((affineCoordinateIso P r).symm _) = _
  rw [RingEquiv.apply_symm_apply, affineCoordinateIso_X]

variable {P} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q)

/-- 元の通常形式の係数射は、元の affine 係数変更と可換。 -/
theorem affineRawPolynomialCoefficient_natural
    (g : Poly (A ⧸ P.ideal) (formVars.{u} r)) :
    affinePolynomialCoefficientMap f r (affineRawPolynomialCoefficient P r g) =
      affineRawPolynomialCoefficient Q r (MvPolynomial.map f.quotientMap g) := by
  have h : (affinePolynomialCoefficientMap f r).comp (affineRawPolynomialCoefficient P r) =
      (affineRawPolynomialCoefficient Q r).comp (MvPolynomial.map f.quotientMap) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change affinePolynomialCoefficientMap f r (affineRawPolynomialCoefficient P r (MvPolynomial.C c)) =
        affineRawPolynomialCoefficient Q r (MvPolynomial.map f.quotientMap (MvPolynomial.C c))
      rw [affineRawPolynomialCoefficient_C, MvPolynomial.map_C,
        affineRawPolynomialCoefficient_C, affinePolynomialCoefficientMap_unit, MvPolynomial.map_C]
    · intro t
      change affinePolynomialCoefficientMap f r (affineRawPolynomialCoefficient P r (MvPolynomial.X t)) =
        affineRawPolynomialCoefficient Q r (MvPolynomial.map f.quotientMap (MvPolynomial.X t))
      rw [affineRawPolynomialCoefficient_X, MvPolynomial.map_X,
        affineRawPolynomialCoefficient_X, affinePolynomialCoefficientMap_X]
  exact RingHom.congr_fun h g

end SerrePositivity.BhattScholze.Prismatic
