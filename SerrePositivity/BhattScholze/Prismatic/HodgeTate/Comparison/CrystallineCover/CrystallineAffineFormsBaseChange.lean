module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineAffineFormsUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineFormsBaseChange

/-!
# 元の affine 完備形式の結晶的な係数拡大

## 概要
元の基底環の通常の係数拡大と、元の affine 完備形式を同定する。

## 方針
元の完備化単位を通して、剰余押し出しで得た通常形式の係数同型を運ぶ。

## 規約
基底係数作用と同じ単項式・外積基底を保つ。HT 比較の同型性は仮定しない。

## 使われ方
特定の Zp 係数変更で、元の標準 HT 写像の定義域の比較を指定する。
-/

public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open SerrePositivity.DeRham
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))
variable (r i : ℕ)

/-- 元の基底環に関する、元の完備形式の係数拡大の指定同型。 -/
def crystallineAffineFormsScalarExtensionEquiv :
    letI := f.toRingHom.toAlgebra
    letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
    letI := Module.compHom (affineForms Q r i) (affineBaseToPolynomialMap Q r)
    B ⊗[A] affineForms P r i ≃ₗ[B] affineForms Q r i := by
  letI := f.toRingHom.toAlgebra
  letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (forms (B ⧸ Q.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk Q.ideal)
  letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
  letI := Module.compHom (affineForms Q r i) (affineBaseToPolynomialMap Q r)
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (crystallineAffineBaseFormsUnitIso P r hPg i).symm) ≪≫ₗ
    prismFormsScalarExtensionEquiv f (formVars.{u} r) i ≪≫ₗ
    crystallineAffineBaseFormsUnitIso Q r hQg i

/-- この比較は、元の単項式・外積基底の完備化単位を同じ基底の単位へ送る。 -/
theorem crystallineAffineFormsScalarExtensionEquiv_basis
    (v : (formVars.{u} r →₀ ℕ) × Set.powersetCard (formVars.{u} r) i) :
    letI := f.toRingHom.toAlgebra
    letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
    letI := Module.compHom (affineForms Q r i) (affineBaseToPolynomialMap Q r)
    crystallineAffineFormsScalarExtensionEquiv f hPg hQg r i
      ((1 : B) ⊗ₜ[A] completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p i
        (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i v)) =
      completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p i
        (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) i v) := by
  letI := f.toRingHom.toAlgebra
  letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (forms (B ⧸ Q.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk Q.ideal)
  letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
  letI := Module.compHom (affineForms Q r i) (affineBaseToPolynomialMap Q r)
  have hs := (crystallineAffineBaseFormsUnitIso P r hPg i).symm_apply_apply
    (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i v)
  rw [crystallineAffineBaseFormsUnitIso_apply] at hs
  simp only [crystallineAffineFormsScalarExtensionEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hs,
    prismFormsScalarExtensionEquiv_basis, crystallineAffineBaseFormsUnitIso_apply]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
