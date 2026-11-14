module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCompletedProjection
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
public import SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Poincare.PDCompletedColumnContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnZero
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 完備分冪 de Rham の第 0 列の同定

## 概要
差座標のない第 0 列を、通常の完備多項式 de Rham 複体へ同定する。

## 方針
未完備係数の同定を完備化し、偏微分との両立を完備化単位で確認する。

## 規約
微分形式の添字は係数環と同じ宇宙に持ち上げる。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の第 0 列への射影の終域。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.DeRham
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

local notation "T" => Vars k r
local notation "ZP" => SerrePositivity.DeRham.Poly k T
local notation "R" => pdRaw k r 0

private def completedZeroCoefficients : pdTerm p k r 0 ≃ₗ[k] completedPoly k T p :=
  let E := zeroTermCoefficients k r
  LinearEquiv.ofLinearMap
    (principalCompletionLinearMap k p (A := R) (B := ZP) E.toLinearMap)
    (principalCompletionLinearMap k p (A := ZP) (B := R) E.symm.toLinearMap)
    (by rw [← principalCompletionLinearMap_comp, LinearEquiv.comp_symm, completionLinearMap_id])
    (by rw [← principalCompletionLinearMap_comp, LinearEquiv.symm_comp, completionLinearMap_id])

private theorem completedZeroCoefficients_partial (t : Fin r) (f : pdTerm p k r 0) :
    completedZeroCoefficients p k r (pdCompletedPartial p k r 0 (.inl t) f) =
      completedPderiv k T p (ULift.up t) (completedZeroCoefficients p k r f) := by
  let E := zeroTermCoefficients k r
  have hd : E.toLinearMap.comp (pdRawPartial k r 0 (.inl t)) =
      (MvPolynomial.pderiv (ULift.up t : T)).toLinearMap.comp E.toLinearMap :=
    LinearMap.ext (zeroTermCoefficients_partial k r t)
  have hpder : principalCompletionLinearMap k p (A := ZP) (B := ZP)
      (MvPolynomial.pderiv (ULift.up t : T)).toLinearMap =
        completedPderiv k T p (ULift.up t) := by
    apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p)
    intro x
    rw [principalCompletionLinearMap_unit]
    exact (completedPderiv_unit k T p (ULift.up t) x).symm
  have h := congrArg (principalCompletionLinearMap k p (A := R) (B := ZP)) hd
  have hc := principalCompletionLinearMap_comp k p (A := R) (B := R) (C := ZP)
    E.toLinearMap (pdRawPartial k r 0 (.inl t))
  have he := principalCompletionLinearMap_comp k p (A := R) (B := ZP) (C := ZP)
    (MvPolynomial.pderiv (ULift.up t : T)).toLinearMap E.toLinearMap
  have h' := hc.symm.trans (h.trans he)
  rw [hpder] at h'
  exact DFunLike.congr_fun h' f

private def completedZeroForms (j : ℕ) :
    (pdRow p k r j).obj ⦋0⦌ ≃ₗ[k] completedPoly k T p ⊗[k] (⋀[k]^j (T → k)) :=
  TensorProduct.congr (completedZeroCoefficients p k r) (zeroExteriorEquiv k r j)

private theorem completedZeroForms_d (j : ℕ) (x : (pdRow p k r j).obj ⦋0⦌) :
    completedZeroForms p k r (j + 1) (pdVerticalD p k r ⦋0⦌ j x) =
      rawD k T p j (completedZeroForms p k r j x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul f w =>
    change pdTerm p k r 0 at f
    change ⋀[k]^j (CopyModule k r ⦋0⦌) at w
    let d := ∑ a : pdCoordinates r 0, TensorProduct.map
      (pdPartial p k r 0 a) (wedgeOne k (CopyModule k r ⦋0⦌) j
        (pdCoordinateOne k r ⦋0⦌ a))
    change completedZeroForms p k r (j + 1) (d (f ⊗ₜ[k] w)) =
      rawD k T p j (completedZeroForms p k r j (f ⊗ₜ[k] w))
    unfold d rawD completedZeroForms
    simp only [LinearMap.sum_apply, TensorProduct.map_tmul, map_sum,
      Fintype.sum_sum_type, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
    refine Fintype.sum_equiv (Equiv.ulift.symm : Fin r ≃ T) _ _ fun t => ?_
    change completedZeroCoefficients p k r (pdPartial p k r 0 (.inl t) f) ⊗ₜ[k]
        zeroExteriorEquiv k r (j + 1)
          (wedgeOne k (CopyModule k r ⦋0⦌) j (pdCoordinateOne k r ⦋0⦌ (.inl t)) w) =
      completedPderiv k T p (ULift.up t) (completedZeroCoefficients p k r f) ⊗ₜ[k]
        wedgeOne k (T → k) j ((exteriorPower.oneEquiv k (T → k)).symm
          (Pi.single (ULift.up t) 1)) (zeroExteriorEquiv k r j w)
    have h := completedZeroCoefficients_partial p k r t f
    change completedZeroCoefficients p k r (pdPartial p k r 0 (.inl t) f) = _ at h
    rw [h]
    congr 1
    change exteriorPower.map (j + 1) (zeroCopyEquiv k r).toLinearMap
      (wedgeOne k (CopyModule k r ⦋0⦌) j (pdCoordinateOne k r ⦋0⦌ (.inl t)) w) = _
    rw [wedgeOne_map, pdCoordinateOne, exteriorPower_map_one, LinearEquiv.coe_coe,
      zeroCopyEquiv_basis]
    rfl

/-- 第 0 列は完備多項式 de Rham 複体と同型。 -/
def pdDeRhamCompletedColumnZeroIso :
    pdDeRhamColumn p k r ⦋0⦌ ≅ completedDeRhamComplex k (formVars.{u} r) p :=
  HomologicalComplex.Hom.isoOfComponents (fun j =>
    ((completedZeroForms p k r j).trans (completedFormsCoeffEquiv k T p j).symm).toModuleIso)
    (by
      intro i j hij
      have h : i + 1 = j := hij
      subst j
      dsimp only [pdDeRhamColumn, completedDeRhamComplex, CochainComplex.of]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change completedDeRhamD k T p i ((completedFormsCoeffEquiv k T p i).symm
        (completedZeroForms p k r i x)) = (completedFormsCoeffEquiv k T p (i + 1)).symm
          (completedZeroForms p k r (i + 1) (pdVerticalD p k r ⦋0⦌ i x))
      apply (completedFormsCoeffEquiv k T p (i + 1)).injective
      rw [completedFormsCoeffEquiv_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact (completedZeroForms_d p k r i x).symm)

/-- 総複体から完備多項式 de Rham 複体への第 0 列の射影。 -/
def pdDeRhamTotalToCompletedForms :
    pdDeRhamTotal p k r ⟶ completedDeRhamComplex k (formVars.{u} r) p :=
  pdDeRhamColumnZeroProjection p k r ≫ (pdDeRhamCompletedColumnZeroIso p k r).hom

/-- 完備多項式 de Rham 複体への射影は擬同型。 -/
theorem pdDeRhamTotalToCompletedForms_quasiIso :
    QuasiIso (pdDeRhamTotalToCompletedForms p k r) := by
  unfold pdDeRhamTotalToCompletedForms
  let := pdDeRhamCompletedColumnZeroProjection_quasiIso p k r
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
