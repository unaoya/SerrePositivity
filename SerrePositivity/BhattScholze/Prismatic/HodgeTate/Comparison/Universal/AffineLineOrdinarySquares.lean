module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CrystallineFormsBasisExt
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryBaseHomology
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedBaseHTBasis
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryHomology

/-!
# 元のηの通常被覆像の零次・一次の正方形

## 概要
元の形式模型の通常係数拡大と、元の被覆上の標準HT写像を同定する。

## 方針
同じ形式の係数同型で移し、元の単項式・外積基底で二つの線形射を照合する。

## 規約
一次の向きの単位の逆を保ち、任意のηの自然性や一般結晶比較を仮定しない。

## 使われ方
HT04.R2の同じηの擬同型性の検査。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded SerrePositivity.DeRham HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
variable (hg : Q.generator = (p : B))
variable (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)

/-- 元の零次形式の係数同型を通した、元のηの正方形。 -/
theorem affineLineOrdinaryBaseRealization_zero_square
    (hη : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (e : (ModuleCat.extendScalars f.toRingHom).obj
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
        (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 0))) ≃ₗ[B]
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap Q 1)).obj
        (ModuleCat.of (affineAlgebra Q 1) (affineForms Q 1 0)))
    (he : ∀ w, e ((1 : B) ⊗ₜ[A,f.toRingHom]
      completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p 0
        (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} 1) 0 w)) =
      completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} 1) p 0
        (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} 1) 0 w)) :
    (affineLineFormalOrdinaryZeroIso P f.toRingHom).hom ≫
      homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 0 ≫
      ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat
        (j := 0) (j' := (0 : ℤ)) rfl).hom =
      ModuleCat.ofHom e.toLinearMap ≫ ModuleCat.ofHom (affineBaseHTMap Q hQ 1 0) := by
  let U := (ModuleCat.restrictScalars (affineBaseToPolynomialMap Q 1)).obj
    (ModuleCat.of (affineAlgebra Q 1) (affineForms Q 1 0))
  let L := (affineLineFormalOrdinaryZeroIso P f.toRingHom).hom ≫
    homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 0 ≫
    ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat
      (j := 0) (j' := (0 : ℤ)) rfl).hom
  let g : U →ₗ[B] (affineBaseComplex Q hQ 1).homology 0 := L.hom.comp e.symm.toLinearMap
  have hh : g = affineBaseHTMap Q hQ 1 0 := by
    apply crystallineForms_basis_ext Q hg 1 0 _
    intro w
    change ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat
      (j := 0) (j' := (0 : ℤ)) rfl).hom
        (homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 0
          ((affineLineFormalOrdinaryZeroIso P f.toRingHom).hom (e.symm _))) = _
    rw [← he w, e.symm_apply_apply,
      affineLineOrdinaryBaseRealization_zero f hP hQ hg η hη]
    rw [he w]
    exact affineAnyBaseHTMap_basis_zero hP 1 f hQ w
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hh (e x)
  change L (e.symm (e x)) = _ at hx
  rw [e.symm_apply_apply] at hx
  exact hx

/-- 元の一次形式の係数同型を通した正方形は、向きの単位の逆を持つ。 -/
theorem affineLineOrdinaryBaseRealization_one_square
    (hη : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1))
    (v : Bˣ) (hv : f.toRingHom P.generator = Q.generator * (v : B))
    (e : (ModuleCat.extendScalars f.toRingHom).obj
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P 1)).obj
        (ModuleCat.of (affineAlgebra P 1) (affineForms P 1 1))) ≃ₗ[B]
      (ModuleCat.restrictScalars (affineBaseToPolynomialMap Q 1)).obj
        (ModuleCat.of (affineAlgebra Q 1) (affineForms Q 1 1)))
    (he : ∀ w, e ((1 : B) ⊗ₜ[A,f.toRingHom]
      completedFormsUnit (A ⧸ P.ideal) (formVars.{u} 1) p 1
        (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} 1) 1 w)) =
      completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} 1) p 1
        (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} 1) 1 w)) :
    letI := Module.compHom (affineForms Q 1 1) (affineBaseToPolynomialMap Q 1)
    (affineLineFormalOrdinaryOneIso P f.toRingHom).hom ≫
      homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 1 ≫
      ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) rfl).hom =
      ModuleCat.ofHom e.toLinearMap ≫
        ModuleCat.ofHom ((((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ 1 1) :
          affineForms Q 1 1 →ₗ[B] (affineBaseComplex Q hQ 1).homology 1) := by
  letI := Module.compHom (affineForms Q 1 1) (affineBaseToPolynomialMap Q 1)
  let U := (ModuleCat.restrictScalars (affineBaseToPolynomialMap Q 1)).obj
    (ModuleCat.of (affineAlgebra Q 1) (affineForms Q 1 1))
  let L := (affineLineFormalOrdinaryOneIso P f.toRingHom).hom ≫
    homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 1 ≫
    ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat
      (j := 1) (j' := (1 : ℤ)) rfl).hom
  let g : U →ₗ[B] (affineBaseComplex Q hQ 1).homology 1 := L.hom.comp e.symm.toLinearMap
  have hh : g = ((v⁻¹ : Bˣ) : B) • affineBaseHTMap Q hQ 1 1 := by
    apply crystallineForms_basis_ext Q hg 1 1 _
    intro w
    change ((affineBaseComplex Q hQ 1).extendHomologyIso ComplexShape.embeddingUpNat
      (j := 1) (j' := (1 : ℤ)) rfl).hom
        (homologyMap (affineLineOrdinaryBaseRealization f hP hQ hg η) 1
          ((affineLineFormalOrdinaryOneIso P f.toRingHom).hom (e.symm _))) = _
    rw [← he w, e.symm_apply_apply,
      affineLineOrdinaryBaseRealization_one f hP hQ hg η hη]
    rw [he w]
    exact affineAnyBaseHTMap_basis_one hP 1 f hQ v hv w
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hh (e x)
  change L (e.symm (e x)) = _ at hx
  rw [e.symm_apply_apply] at hx
  exact hx

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
