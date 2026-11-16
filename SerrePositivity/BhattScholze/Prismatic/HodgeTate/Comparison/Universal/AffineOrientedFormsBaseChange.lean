module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletedFormsZeroBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineAffineFormsBaseChange

/-!
# 元の向き付き基底から結晶的被覆への形式の通常底変換

## 概要
始域の生成元をpと仮定せず、元の完備形式の通常係数拡大を同定する。

## 方針
元の基底作用を剰余上の作用へ戻し、剰余の押し出しとpで零化された係数への同型を合成する。

## 規約
終域の生成元だけをpとする。元の単項式と外積の基底の単位を保つ。

## 使われ方
元のaffine lineの標準HT写像の零次・一次を被覆上で照合する。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open CategoryTheory SerrePositivity.DeRham HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (r i : ℕ)

/-- 元の剰余係数作用を持つ完備形式の加群。 -/
def affineCompletedFormsBaseModule : ModuleCat.{u} A := by
  letI := Module.compHom (completedForms (A ⧸ P.ideal) (formVars.{u} r) p i)
    (Ideal.Quotient.mk P.ideal)
  exact ModuleCat.of A (completedForms (A ⧸ P.ideal) (formVars.{u} r) p i)

/-- 元のaffine基底作用は、同じ完備形式の剰余係数作用に一致する。 -/
def affineBaseFormsActionIso : affineCompletedFormsBaseModule P r i ≅
    (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
      (ModuleCat.of (affineAlgebra P r) (affineForms P r i)) := by
  let M := affineCompletedFormsBaseModule P r i
  let N := (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
    (ModuleCat.of (affineAlgebra P r) (affineForms P r i))
  let e : M ≃ₗ[A] N :=
    { __ := AddEquiv.refl _
      map_smul' := fun a w => by
        let w' : completedForms (A ⧸ P.ideal) (formVars.{u} r) p i := w
        change Ideal.Quotient.mk P.ideal a • w' =
          affineCoordinateIso P r (affineBaseToPolynomialMap P r a) • w'
        rw [affineCoordinateIso_base]
        change _ = algebraMap (A ⧸ P.ideal)
          (completedPoly (A ⧸ P.ideal) (formVars.{u} r) p)
          (Ideal.Quotient.mk P.ideal a) • w'
        exact (algebraMap_smul _ _ _).symm }
  exact e.toModuleIso


variable {P} {Q : OrientedPrism p B} (f : OrientedPrism.Hom P Q)
variable (hg : Q.generator = (p : B))
include hg

/-- 元の始域を結晶的に制限せず、完備形式の通常係数拡大は同じ基底の単位を保つ。 -/
theorem exists_affineOrientedFormsBaseChangeEquiv :
    let U := (ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj
      (ModuleCat.of (affineAlgebra P r) (affineForms P r i))
    let V := (ModuleCat.restrictScalars (affineBaseToPolynomialMap Q r)).obj
      (ModuleCat.of (affineAlgebra Q r) (affineForms Q r i))
    letI := f.toRingHom.toAlgebra
    ∃ e : ((ModuleCat.extendScalars f.toRingHom).obj U) ≃ₗ[B] V,
      ∀ v : (formVars.{u} r →₀ ℕ) × Set.powersetCard (formVars.{u} r) i,
        e ((1 : B) ⊗ₜ[A] (show U from completedFormsUnit (A ⧸ P.ideal) (formVars.{u} r) p i
          (polynomialFormsBasis (A ⧸ P.ideal) (formVars.{u} r) i v))) =
          completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p i
            (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) i v) := by
  let K := A ⧸ P.ideal
  let L := B ⧸ Q.ideal
  let T := formVars.{u} r
  let M := completedForms K T p i
  letI := f.toRingHom.toAlgebra
  letI := f.quotientMap.toAlgebra
  letI := prismResidueScalarTower f
  letI := prismResidue_isPushout f
  letI := Module.compHom M (Ideal.Quotient.mk P.ideal)
  letI := Module.compHom (forms L T i) (Ideal.Quotient.mk Q.ideal)
  letI : IsScalarTower A K M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower B L (forms L T i) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨ec, hc⟩ := exists_completedFormsZeroBaseChangeEquiv K L T p
    (crystallineResidue_p_zero Q hg) i
  let e0 := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
    (affineBaseFormsActionIso P r i).toLinearEquiv.symm
  let e := e0 ≪≫ₗ (Algebra.IsPushout.cancelBaseChange A B K L M).symm ≪≫ₗ
    ec.restrictScalars B ≪≫ₗ crystallineAffineBaseFormsUnitIso Q r hg i
  refine ⟨e, ?_⟩
  intro v
  change crystallineAffineBaseFormsUnitIso Q r hg i
    (ec ((Algebra.IsPushout.cancelBaseChange A B K L M).symm
      ((1 : B) ⊗ₜ[A] completedFormsUnit K T p i (polynomialFormsBasis K T i v)))) = _
  erw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, hc,
    crystallineAffineBaseFormsUnitIso_apply]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
