module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineFormsReduction
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffinePolynomial

/-!
# 元の基底作用に関する結晶的な形式の完備化単位

## 概要
通常形式から元の affine 完備形式への単位を、元の基底環に関する線形同型にする。

## 方針
係数定数上で変数の改名と完備化単位が可換であることを使う。

## 規約
基底作用は元の剰余写像と元の affine 係数構造射を通じた作用に固定する。

## 使われ方
特定の Zp 係数変更で、元の標準 HT 写像の定義域を同定する。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open CategoryTheory SerrePositivity.DeRham SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (r : ℕ)

/-- 元の座標改名は、元の基底係数の完備化単位を保つ。 -/
theorem affineCoordinateIso_base (a : A) :
    affineCoordinateIso P r (affineBaseToPolynomialMap P r a) =
      algebraMap (Poly (A ⧸ P.ideal) (formVars.{u} r))
        (completedPoly (A ⧸ P.ideal) (formVars.{u} r) p)
        (MvPolynomial.C (Ideal.Quotient.mk P.ideal a)) := by
  have h := coord_map_C P r (Ideal.Quotient.mk P.ideal a)
  have ht := (IsScalarTower.algebraMap_apply (A ⧸ P.ideal)
    (Poly (A ⧸ P.ideal) (formVars.{u} r))
    (completedPoly (A ⧸ P.ideal) (formVars.{u} r) p) (Ideal.Quotient.mk P.ideal a)).symm
  rw [← ht] at h
  simpa only [e, affineBaseToPolynomialMap, RingHom.comp_apply,
    prismPolynomialAlgebra, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq] using h

/-- 通常の係数定数は、元の基底係数構造射と一致する。 -/
theorem rawCoefficient_base (a : A) :
    (affineCoordinateIso P r).symm
      (algebraMap (Poly (A ⧸ P.ideal) (formVars.{u} r))
        (completedPoly (A ⧸ P.ideal) (formVars.{u} r) p)
        (MvPolynomial.C (Ideal.Quotient.mk P.ideal a))) =
      affineBaseToPolynomialMap P r a := by
  apply (affineCoordinateIso P r).injective
  change affineCoordinateIso P r ((affineCoordinateIso P r).symm _) = _
  rw [RingEquiv.apply_symm_apply, affineCoordinateIso_base]

/-- 元の基底環に関する、通常形式から元の完備形式への単位。 -/
def affineBaseFormsUnit (i : ℕ) :
    letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
    letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
    forms (A ⧸ P.ideal) (formVars.{u} r) i →ₗ[A] affineForms P r i := by
  letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
  exact
    { __ := completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p i
      map_smul' := fun a w => by
        change completedFormsUnit _ _ p i (Ideal.Quotient.mk P.ideal a • w) =
          affineBaseToPolynomialMap P r a • completedFormsUnit _ _ p i w
        have h := completedFormsUnit_smul_raw P r i
          (MvPolynomial.C (Ideal.Quotient.mk P.ideal a)) w
        change completedFormsUnit _ _ p i (MvPolynomial.C (Ideal.Quotient.mk P.ideal a) • w) =
          (affineCoordinateIso P r).symm
            (algebraMap (Poly (A ⧸ P.ideal) (formVars.{u} r))
              (completedPoly (A ⧸ P.ideal) (formVars.{u} r) p)
              (MvPolynomial.C (Ideal.Quotient.mk P.ideal a))) •
              completedFormsUnit _ _ p i w at h
        rw [rawCoefficient_base] at h
        simpa only [← MvPolynomial.algebraMap_eq, algebraMap_smul] using h }

variable (hg : P.generator = (p : A))
include hg

/-- 選択生成元が p なら、元の基底作用に関する完備化単位は線形同型。 -/
def crystallineAffineBaseFormsUnitIso (i : ℕ) :
    letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
    letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
    forms (A ⧸ P.ideal) (formVars.{u} r) i ≃ₗ[A] affineForms P r i := by
  letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
  apply LinearEquiv.ofBijective (affineBaseFormsUnit P r i)
  let e := crystallineCompletedFormsReductionIso P hg (formVars.{u} r) i
  have h (w : forms (A ⧸ P.ideal) (formVars.{u} r) i) :
      e (affineBaseFormsUnit P r i w) = w :=
    crystallineCompletedFormsReductionIso_unit P hg (formVars.{u} r) i w
  constructor
  · intro x y he
    exact (h x).symm.trans ((congrArg e he).trans (h y))
  · intro z
    exact ⟨e z, e.injective (h (e z))⟩

/-- 同型は元の通常形式の完備化単位そのもの。 -/
@[simp] theorem crystallineAffineBaseFormsUnitIso_apply (i : ℕ)
    (w : forms (A ⧸ P.ideal) (formVars.{u} r) i) :
    crystallineAffineBaseFormsUnitIso P r hg i w =
      completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p i w := by
  simp only [crystallineAffineBaseFormsUnitIso, LinearEquiv.ofBijective_apply,
    affineBaseFormsUnit, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
