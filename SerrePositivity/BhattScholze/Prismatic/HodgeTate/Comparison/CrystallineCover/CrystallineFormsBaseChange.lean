module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineFormsCoefficientBasis
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.PrismResidueScalarTensor

/-!
# 元の prism 基底環による通常形式の係数拡大

## 概要
元の基底環の係数拡大を、元の剰余環上の通常の多項式形式へ移す。

## 方針
剰余係数の押し出しの標準テンソル同型と、同じ単項式・外積基底の係数同型を合成する。

## 規約
形式上の基底環の作用は元の剰余写像を通じたもの。一般の HT 比較は使わない。

## 使われ方
特定の Zp 係数射で、標準 HT 写像の定義域の係数拡大を計算する。
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
variable (T : Type u) [Fintype T] [LinearOrder T]
local notation "K" => A ⧸ P.ideal
local notation "L" => B ⧸ Q.ideal

/-- 元の基底環の通常の係数拡大で計算する、元の剰余上の通常形式の線形同型。 -/
def prismFormsScalarExtensionEquiv (i : ℕ) :
    letI := f.toRingHom.toAlgebra
    letI := Module.compHom (forms K T i) (Ideal.Quotient.mk P.ideal)
    letI := Module.compHom (forms L T i) (Ideal.Quotient.mk Q.ideal)
    B ⊗[A] forms K T i ≃ₗ[B] forms L T i := by
  letI := f.toRingHom.toAlgebra
  letI := f.quotientMap.toAlgebra
  letI := prismResidueScalarTower f
  letI := prismResidue_isPushout f
  letI := Module.compHom (forms K T i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (forms L T i) (Ideal.Quotient.mk Q.ideal)
  letI : IsScalarTower A K (forms K T i) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower B L (forms L T i) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (Algebra.IsPushout.cancelBaseChange A B K L (forms K T i)).symm ≪≫ₗ
    (crystallineFormsCoefficientBaseChangeEquiv K L T i).restrictScalars B

/-- この同型は、元の単項式と外積の基底の単位純テンソルを保つ。 -/
theorem prismFormsScalarExtensionEquiv_basis (i : ℕ)
    (v : (T →₀ ℕ) × Set.powersetCard T i) :
    letI := f.toRingHom.toAlgebra
    letI := Module.compHom (forms K T i) (Ideal.Quotient.mk P.ideal)
    letI := Module.compHom (forms L T i) (Ideal.Quotient.mk Q.ideal)
    prismFormsScalarExtensionEquiv f T i ((1 : B) ⊗ₜ[A] polynomialFormsBasis K T i v) =
      polynomialFormsBasis L T i v := by
  letI := f.toRingHom.toAlgebra
  letI := f.quotientMap.toAlgebra
  letI := prismResidueScalarTower f
  letI := prismResidue_isPushout f
  letI := Module.compHom (forms K T i) (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (forms L T i) (Ideal.Quotient.mk Q.ideal)
  letI : IsScalarTower A K (forms K T i) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower B L (forms L T i) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change crystallineFormsCoefficientBaseChangeEquiv K L T i
    ((Algebra.IsPushout.cancelBaseChange A B K L (forms K T i)).symm
      ((1 : B) ⊗ₜ[A] polynomialFormsBasis K T i v)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one,
    crystallineFormsCoefficientBaseChangeEquiv_basis]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
