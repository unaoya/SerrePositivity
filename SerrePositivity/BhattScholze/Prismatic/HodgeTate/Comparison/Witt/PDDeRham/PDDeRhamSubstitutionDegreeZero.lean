module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionGenerators
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionForms
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamSubstitutionJacobian
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamSubstitutionChainRule
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegree

/-!
# 完備分冪 de Rham の次数 0 の代入

## 概要
次数 0 の代入が係数の代入になり、次数 0 の微分と可換であることを示す。

## 方針
次数 1 の生成元公式と、完備偏微分の連鎖律を組み合わせる。

## 規約
係数を 0 形式に入れるときは、次数 0 の外冪の単位とテンソルする。

## 使われ方
BS 著者版 Theorem 6.4 の多項式代入を余鎖写像にする。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DeRham SerrePositivity.DerivedCompletion
open SerrePositivity.KST.DerivedBlowup
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime]
variable {J : Ideal k} (γ : DividedPowers J)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hr : Function.Injective (fun x : k => (p : k) * x))
variable {Q Q' : Poly k} (f : Q ⟶ Q') (n : ℕ)

local notation "S" => pdTerm p k Q.n n
local notation "T" => pdTerm p k Q'.n n
local notation "M" => ((Fin Q.n × Fin (n + 1)) →₀ k)
local notation "N" => ((Fin Q'.n × Fin (n + 1)) →₀ k)
local notation "φ" => substituteCompleted p γ hk hr f n
local notation "U" => principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k Q'.n n))
local notation "bS" => pdCoordinateBasis k Q.n ⦋n⦌
local notation "bT" => pdCoordinateBasis k Q'.n ⦋n⦌

private theorem exteriorZero_one {V : Type u} [AddCommGroup V] [Module k V] :
    ((exteriorPower.zeroEquiv k V).symm 1).val = 1 := by
  simp [exteriorPower.zeroEquiv, exteriorPower.ιMulti, ExteriorAlgebra.ιMulti_apply]

/-- 次数 0 の外冪の単位を添えた係数に対し、形式の代入は係数の代入を誘導する。 -/
theorem substituteForms_zero (x : S) :
    substituteForms p γ hk hr f n 0 (x ⊗ₜ[k] (exteriorPower.zeroEquiv k M).symm 1) =
      φ x ⊗ₜ[k] (exteriorPower.zeroEquiv k N).symm 1 := by
  apply exteriorBaseChangeDegreeInclusion_injective 0
  rw [map_inclusion]
  change substituteExterior p γ hk hr f n
      (x ⊗ₜ[k] ((exteriorPower.zeroEquiv k M).symm 1).val) =
    φ x ⊗ₜ[k] ((exteriorPower.zeroEquiv k N).symm 1).val
  simp only [exteriorZero_one]
  change substituteExterior p γ hk hr f n (algebraMap S _ x) = algebraMap T _ (φ x)
  unfold substituteExterior
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, map_one]
  exact (exteriorToBaseChange.comp ((ExteriorAlgebra.map (completedJacobian p f n)).comp
    exteriorOfBaseChange)).commutes (φ x)

omit [Fact p.Prime] in
private theorem completedJacobian_vertex (j : Fin Q.n) (i : Fin (n + 1)) :
    completedJacobian p f n ((1 : T) ⊗ₜ[k] Finsupp.single (j,i) 1) =
      ∑ b : pdCoordinates Q'.n n, U (vertexPartial f n i b (MvPolynomial.X j)) ⊗ₜ[k] bT b := by
  simp only [completedJacobian, LinearMap.liftBaseChange_tmul, one_smul,
    LinearMap.comp_apply, jacobianOnCopies_single, map_sum, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rfl

omit [Fact p.Prime] in
private theorem completedJacobian_coordinate (a : pdCoordinates Q.n n) :
    completedJacobian p f n ((1 : T) ⊗ₜ[k] bS a) =
      ∑ b : pdCoordinates Q'.n n, U (jacobian f n b a) ⊗ₜ[k] bT b := by
  rw [pdCoordinateBasis_apply]
  rcases a with j | ⟨j,i⟩
  · exact completedJacobian_vertex p f n j 0
  · change completedJacobian p f n
      ((1 : T) ⊗ₜ[k] (Finsupp.single (j,i.succ) 1 - Finsupp.single (j,0) 1)) = _
    rw [TensorProduct.tmul_sub, map_sub, completedJacobian_vertex, completedJacobian_vertex,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [jacobian, map_sub, TensorProduct.sub_tmul]

private theorem wedgeOne_zero_unit {V : Type u} [AddCommGroup V] [Module k V] (v : ⋀[k]^1 V) :
    wedgeOne k V 0 v ((exteriorPower.zeroEquiv k V).symm 1) = v := by
  apply Subtype.ext
  rw [wedgeOne_coe, exteriorZero_one, mul_one]

omit [Fact p.Prime] in
private theorem d_zero_tmul (r : ℕ) (x : pdTerm p k r n) :
    pdVerticalD p k r ⦋n⦌ 0 (x ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k r ⦋n⦌)).symm 1) =
      ∑ a : pdCoordinates r n, pdPartial p k r n a x ⊗ₜ[k] pdCoordinateOne k r ⦋n⦌ a := by
  change (∑ a : pdCoordinates r n, TensorProduct.map (pdPartial p k r n a)
    (wedgeOne k _ 0 (pdCoordinateOne k r ⦋n⦌ a)))
    (x ⊗ₜ[k] (exteriorPower.zeroEquiv k (CopyModule k r ⦋n⦌)).symm 1) = _
  simp only [LinearMap.sum_apply, TensorProduct.map_tmul, wedgeOne_zero_unit]

private theorem substituteForms_coordinate (x : S) (a : pdCoordinates Q.n n) :
    substituteForms p γ hk hr f n 1 (x ⊗ₜ[k] pdCoordinateOne k Q.n ⦋n⦌ a) =
      ∑ b : pdCoordinates Q'.n n, (φ x * U (jacobian f n b a)) ⊗ₜ[k]
        pdCoordinateOne k Q'.n ⦋n⦌ b := by
  have h (r : ℕ) (a : pdCoordinates r n) : pdCoordinateOne k r ⦋n⦌ a =
      (exteriorPower.oneEquiv k _).symm (pdCoordinateBasis k r ⦋n⦌ a) := by
    rw [pdCoordinateBasis_apply]
    rfl
  rw [h Q.n, substituteForms_one]
  rw [show φ x ⊗ₜ[k] bS a = φ x • ((1 : T) ⊗ₜ[k] bS a) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, completedJacobian_coordinate]
  simp only [Finset.smul_sum, map_sum, TensorProduct.smul_tmul', smul_eq_mul,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe, h]

/-- 次数 0 の分冪 de Rham 微分は多項式代入と可換。 -/
theorem substituteRowForms_d_zero :
    substituteRowForms p γ hk hr f n 0 ≫ pdVerticalD p k Q'.n ⦋n⦌ 0 =
      pdVerticalD p k Q.n ⦋n⦌ 0 ≫ substituteRowForms p γ hk hr f n 1 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x w
  change S at x
  obtain ⟨c, rfl⟩ := (exteriorPower.zeroEquiv k M).symm.surjective w
  have h : (exteriorPower.zeroEquiv k M).symm c =
      c • (exteriorPower.zeroEquiv k M).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h, ← TensorProduct.smul_tmul]
  change pdVerticalD p k Q'.n ⦋n⦌ 0
      (substituteForms p γ hk hr f n 0 ((c • x) ⊗ₜ[k] (exteriorPower.zeroEquiv k M).symm 1)) =
    substituteForms p γ hk hr f n 1
      (pdVerticalD p k Q.n ⦋n⦌ 0 ((c • x) ⊗ₜ[k] (exteriorPower.zeroEquiv k M).symm 1))
  rw [substituteForms_zero, d_zero_tmul, d_zero_tmul, map_sum]
  simp_rw [substituteForms_coordinate]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← TensorProduct.sum_tmul]
  congr 1
  change pdCompletedPartial p k Q'.n n b (φ (c • x)) = _
  rw [substituteCompleted_partial]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
