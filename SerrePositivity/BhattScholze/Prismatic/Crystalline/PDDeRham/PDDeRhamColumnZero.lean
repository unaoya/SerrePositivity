module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineForms
import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBasis
public import SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDRawDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawDifferential
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex

/-!
# pd de Rham 第 0 列の多項式表示

## 概要
第 0 列には差座標がないので、標数 p では通常の多項式 de Rham 複体と同型。

## 方針
空の分冪基底の係数を取り出し、頂点の一次形式を通常の dX へ移す。

## 規約
微分形式の添字は係数環と同じ宇宙に持ち上げる。

## 使われ方
pd Čech コホモロジーと Cartier の比較。
-/

public noncomputable section

open CategoryTheory DividedPowerAlgebra SerrePositivity.DeRham
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (k : Type u) [CommRing k] (r : ℕ)

private abbrev Vars (_k : Type u) (r : ℕ) : Type u := formVars r
local notation "T" => Vars k r
local notation "D" => DividedPowerAlgebra k ((Fin r × Fin 0) →₀ k)

private def noDifferenceCoefficients : D ≃ₗ[k] k :=
  (freeDPBasis (Fin r × Fin 0) k).repr.trans (Finsupp.uniqueLinearEquiv k k 0)

private def zeroTermCoefficients : pdRaw k r 0 ≃ₗ[k] Poly k T :=
  (TensorProduct.congr (MvPolynomial.renameEquiv k
    (Equiv.ulift.symm : Fin r ≃ T)).toLinearEquiv (noDifferenceCoefficients k r)).trans
    (TensorProduct.rid k _)

private def zeroCopyIndex : Fin r × Fin 1 ≃ T where
  toFun a := ULift.up a.1
  invFun a := (a.down, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

private def zeroCopyEquiv : CopyModule k r ⦋0⦌ ≃ₗ[k] T → k :=
  (Finsupp.domLCongr (R := k) (M := k) (zeroCopyIndex k r)).trans
    (Finsupp.linearEquivFunOnFinite k k T)

private theorem zeroCopyEquiv_basis (t : Fin r) :
    zeroCopyEquiv k r (pdCoordinateVector k r ⦋0⦌ (.inl t)) =
      Pi.single (ULift.up t : T) 1 := by
  change zeroCopyEquiv k r (Finsupp.single (t, 0) 1) = _
  rw [zeroCopyEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  simp [zeroCopyIndex]

private def zeroExteriorEquiv (j : ℕ) :
    (⋀[k]^j (CopyModule k r ⦋0⦌)) ≃ₗ[k] (⋀[k]^j (T → k)) :=
  let E := zeroCopyEquiv k r
  LinearEquiv.ofLinearMap (exteriorPower.map j E.toLinearMap)
    (exteriorPower.map j E.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, LinearEquiv.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, LinearEquiv.symm_comp, exteriorPower.map_id])

private def zeroFormsEquiv (j : ℕ) :
    pdRawForms k r ⦋0⦌ j ≃ₗ[k] forms k T j :=
  TensorProduct.congr (zeroTermCoefficients k r) (zeroExteriorEquiv k r j)

private theorem zeroTermCoefficients_partial (t : Fin r) (f : pdRaw k r 0) :
    zeroTermCoefficients k r (pdRawPartial k r 0 (.inl t) f) =
      MvPolynomial.pderiv (ULift.up t : T) (zeroTermCoefficients k r f) := by
  induction f using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f g =>
    rw [partial_inl_tmul]
    change noDifferenceCoefficients k r g • MvPolynomial.rename ULift.up (MvPolynomial.pderiv t f) =
      MvPolynomial.pderiv (ULift.up t : T)
        (noDifferenceCoefficients k r g • MvPolynomial.rename ULift.up f)
    rw [Derivation.map_smul, MvPolynomial.pderiv_rename ULift.up_injective]

set_option synthInstance.maxHeartbeats 80000 in
-- 外冪の宇宙をそろえた基底変更に伴う加群構造を照合する。
private theorem zeroFormsEquiv_d (j : ℕ) (x : pdRawForms k r ⦋0⦌ j) :
    zeroFormsEquiv k r (j + 1) (pdRawVertical k r ⦋0⦌ j x) =
      deRhamD k T j (zeroFormsEquiv k r j x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f w =>
    change pdRaw k r 0 at f
    change ⋀[k]^j (CopyModule k r ⦋0⦌) at w
    unfold pdRawVertical deRhamD deRhamDLinear zeroFormsEquiv
    simp only [LinearMap.sum_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.congr_tmul,
      TensorProduct.map_tmul, map_sum, Fintype.sum_sum_type, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
    refine Fintype.sum_equiv (Equiv.ulift.symm : Fin r ≃ T) _ _ fun t => ?_
    rw [zeroTermCoefficients_partial]
    congr 1
    change exteriorPower.map (j + 1) (zeroCopyEquiv k r).toLinearMap
      (wedgeOne k (CopyModule k r ⦋0⦌) j (pdCoordinateOne k r ⦋0⦌ (.inl t)) w) = _
    rw [wedgeOne_map, pdCoordinateOne, exteriorPower_map_one, LinearEquiv.coe_coe, zeroCopyEquiv_basis]
    rfl

variable (p : ℕ) (hp : (p : k) = 0)

/-- 標数 p での第 0 列は通常の多項式 de Rham 複体。 -/
def pdDeRhamColumnZeroIso :
    pdDeRhamColumn p k r ⦋0⦌ ≅ deRhamComplex k (formVars.{u} r) :=
  (pdRawDeRhamColumnIso p k r hp ⦋0⦌).symm ≪≫
    HomologicalComplex.Hom.isoOfComponents (fun j => (zeroFormsEquiv k r j).toModuleIso) (by
      intro j j' hj
      have hh : j + 1 = j' := hj
      subst j'
      dsimp only [pdRawDeRhamColumn, deRhamComplex, CochainComplex.of]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (zeroFormsEquiv_d k r j x).symm)

end SerrePositivity.BhattScholze.Prismatic
