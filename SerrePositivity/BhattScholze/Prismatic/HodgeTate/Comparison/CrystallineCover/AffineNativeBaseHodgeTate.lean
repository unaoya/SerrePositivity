module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCohomologyClasses
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineAffineFormsUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCohomologyClasses
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineAffineFormsUnit
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineRawHodgeTateWords
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateModule
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass

/-!
# 元の余輪体表示による基底線形な標準 HT 写像

## 概要
元の通常形式上の標準 HT 写像を、同じ基底複体のホモロジーへの線形写像として読む。

## 方針
元の二つの係数作用の一致を、同じ余輪体の類で確認する。

## 規約
元の標準 HT 写像の値も、同じ余輪体の代表も変更しない。

## 使われ方
特定の Zp 係数変更で、通常形式の係数拡大と元のコホモロジー同型を結ぶ。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open SerrePositivity.DeRham SerrePositivity.Cosimplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の加法的な基底ホモロジー同型は、元の多項式作用を制限した基底作用で線形。 -/
theorem affineNativeBaseCohomologyEquiv_smul (i : ℕ) (a : A)
    (z : hodgeTateCohomology' P hP r i) :
    letI := htModule P hP r i
    affineNativeBaseCohomologyEquiv P hP r i (affineBaseToPolynomialMap P r a • z) =
      a • affineNativeBaseCohomologyEquiv P hP r i z := by
  letI := htModule P hP r i
  let X := reducedModel P hP r
  let ι := affineBaseCoefficients P hP r
  obtain ⟨c, rfl⟩ := cohomologyClass_surjective X i z
  let x : X.obj ⦋i⦌ := c.1
  let c₀ : (moduleCochains A X ι).X i := c.1
  let c' : Cocycles X i := ⟨(ι.app ⦋i⦌) a * x, by
    change (ringCochainComplex X).d i (i + 1) _ = 0
    rw [ringCochainComplex_d_apply, ← moduleCochains_d_apply A X ι i]
    change (moduleCochains A X ι).d i (i + 1) (a • c₀) = 0
    rw [map_smul, moduleCycle A X ι i c, smul_zero]⟩
  have hr : affineHTCycleRep P hP r i c' =
      affineBaseToPolynomialMap P r a • affineHTCycleRep P hP r i c := by
    apply (ModuleCat.mono_iff_injective ((affineHTComplex P hP r).iCycles i)).mp inferInstance
    rw [affineHTCycleRep_i, map_smul, affineHTCycleRep_i]
    change (affineBaseCoefficients P hP r).app ⦋i⦌ a * x =
      (affineHTCoefficients P hP r).app ⦋i⦌ (affineBaseToPolynomialMap P r a) * x
    rw [affineHTCoefficients_base]
  have ha : affineNativeBaseCycleRep P hP r i c' = a • affineNativeBaseCycleRep P hP r i c := by
    apply (ModuleCat.mono_iff_injective ((affineBaseComplex P hP r).iCycles i)).mp inferInstance
    rw [map_smul]
    simp only [affineNativeBaseCycleRep, moduleCycleRep_apply]
    change (ι.app ⦋i⦌) a * x = (ι.app ⦋i⦌) a * x
    rfl
  have hs : affineBaseToPolynomialMap P r a • cohomologyClass X i c = cohomologyClass X i c' := by
    apply (affineHTCohomologyEquiv P hP r i).injective
    rw [map_smul, affineHTCohomologyEquiv_class, affineHTCohomologyEquiv_class, hr, map_smul]
  rw [hs, affineNativeBaseCohomologyEquiv_class, ha, map_smul,
    affineNativeBaseCohomologyEquiv_class]

/-- 元の通常形式上の標準 HT 写像を、元の基底環上の線形写像として読む。 -/
def affineNativeRawHTMap (i : ℕ) :
    letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
    forms (A ⧸ P.ideal) (formVars.{u} r) i →ₗ[A] (affineBaseComplex P hP r).homology i := by
  letI := Module.compHom (forms (A ⧸ P.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk P.ideal)
  letI := htModule P hP r i
  letI := Module.compHom (affineForms P r i) (affineBaseToPolynomialMap P r)
  exact
    { __ := (affineNativeBaseCohomologyEquiv P hP r i).toAddMonoidHom.comp (affineHTRawMap P hP r i)
      map_smul' := fun a w => by
        have h := (affineBaseFormsUnit P r i).map_smul a w
        change completedFormsUnit _ _ p i (a • w) =
          affineBaseToPolynomialMap P r a • completedFormsUnit _ _ p i w at h
        change affineNativeBaseCohomologyEquiv P hP r i
          ((hodgeTateMap P hP r).app i (completedFormsUnit _ _ p i (a • w))) = _
        rw [h, map_smul, affineNativeBaseCohomologyEquiv_smul]
        rfl }

/-- 選択生成元が p のとき、同じ通常形式の線形写像の全単射性は元の HT 写像と同値。 -/
theorem affineNativeRawHTMap_bijective_iff (hg : P.generator = (p : A)) (i : ℕ) :
    Function.Bijective (affineNativeRawHTMap P hP r i) ↔
      Function.Bijective ((hodgeTateMap P hP r).app i) := by
  let e := affineNativeBaseCohomologyEquiv P hP r i
  let u := crystallineAffineBaseFormsUnitIso P r hg i
  have h : (affineNativeRawHTMap P hP r i : _ → _) =
      e ∘ ((hodgeTateMap P hP r).app i) ∘ u := by
    funext w
    simp only [affineNativeRawHTMap, LinearMap.coe_mk, AddMonoidHom.comp_apply,
      affineHTRawMap, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      crystallineAffineBaseFormsUnitIso_apply]
    rfl
  rw [h, Function.Bijective.of_comp_iff' e.bijective,
    Function.Bijective.of_comp_iff _ u.bijective]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
