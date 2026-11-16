module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineNativeBaseHodgeTate
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.PrismResidueTensorExt
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineFormsBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineNativeBaseHodgeTate

/-!
# 元の標準 HT 写像と結晶係数変更の正方形

## 概要
通常形式の係数同型と元の基底コホモロジー同型が、同じ標準 HT 写像と可換であることを示す。

## 方針
剰余係数の基底上の自然性を、元の基底環への係数の持ち上げで線形写像全体へ延ばす。

## 規約
両側の同型は既に指定したものを使う。一般の結晶 HT 比較は使わない。

## 使われ方
既知の Zp の標準 HT 同型を、特定の Construction 6.1 の被覆へ運ぶ。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open SerrePositivity.DeRham
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hPg : P.generator = (p : A)) (hQg : Q.generator = (p : B))
variable (hf : f.toRingHom.Flat) (r i : ℕ)

/-- 同じ標準 HT 写像は、元の形式と基底コホモロジーの指定された係数同型と可換。 -/
theorem affineCrystallineRawHT_square :
    letI := f.toRingHom.toAlgebra
    letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
    letI := Module.compHom (forms (B ⧸ Q.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk Q.ideal)
    (ModuleCat.extendScalars f.toRingHom).map (ModuleCat.ofHom (affineNativeRawHTMap P hP r i)) ≫
        (affineCrystallineBaseCohomologyIso f hP hQ hPg hQg hf r i).hom =
      (prismFormsScalarExtensionEquiv f (formVars.{u} r) i).toModuleIso.hom ≫
        ModuleCat.ofHom (affineNativeRawHTMap Q hQ r i) := by
  letI := f.toRingHom.toAlgebra
  letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (forms (B ⧸ Q.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk Q.ideal)
  apply ModuleCat.hom_ext
  apply residueCoefficientTensor_ext f.toRingHom P.ideal
    (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i)
  intro v
  change (affineCrystallineBaseCohomologyIso f hP hQ hPg hQg hf r i).hom
      ((1 : B) ⊗ₜ[A] affineNativeRawHTMap P hP r i
        (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i v)) =
    affineNativeRawHTMap Q hQ r i (prismFormsScalarExtensionEquiv f (formVars.{u} r) i
      ((1 : B) ⊗ₜ[A] polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i v))
  rw [prismFormsScalarExtensionEquiv_basis]
  change (affineCrystallineBaseCohomologyIso f hP hQ hPg hQg hf r i).hom
      ((1 : B) ⊗ₜ[A] affineNativeBaseCohomologyEquiv P hP r i
        (affineHTRawMap P hP r i (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i v))) =
    affineNativeBaseCohomologyEquiv Q hQ r i
      (affineHTRawMap Q hQ r i (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) i v))
  rw [affineCrystallineBaseCohomologyIso_one_tmul, affineHTRawMap_basis_natural]

include f hPg hQg hf

/-- 元の始域で標準 HT が同型なら、平坦な結晶係数変更先でも同じ標準写像が同型。 -/
theorem affineCrystallineRawHT_transfer (h : HodgeTateIsoStatement P hP r) :
    HodgeTateIsoStatement Q hQ r := by
  intro i
  apply (affineNativeRawHTMap_bijective_iff Q hQ r hQg i).mp
  letI := f.toRingHom.toAlgebra
  letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (forms (B ⧸ Q.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk Q.ideal)
  let F := ModuleCat.extendScalars f.toRingHom
  let s := ModuleCat.ofHom (affineNativeRawHTMap P hP r i)
  let t := ModuleCat.ofHom (affineNativeRawHTMap Q hQ r i)
  let E := (prismFormsScalarExtensionEquiv f (formVars.{u} r) i).toModuleIso
  haveI : IsIso s := (ConcreteCategory.isIso_iff_bijective s).mpr
    ((affineNativeRawHTMap_bijective_iff P hP r hPg i).mpr (h i))
  have he : t = E.inv ≫ F.map s ≫
      (affineCrystallineBaseCohomologyIso f hP hQ hPg hQg hf r i).hom := by
    rw [affineCrystallineRawHT_square f hP hQ hPg hQg hf r i]
    change t = E.inv ≫ E.hom ≫ t
    simp only [Iso.inv_hom_id_assoc]
  haveI : IsIso t := by
    rw [he]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective t).mp inferInstance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
