module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawDifferential
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial

/-!
# pd de Rham の各列の微分

## 概要
完備分冪係数の偏微分を用いて、pd de Rham の各列を余鎖複体にする。

## 方針
第 0 頂点と差座標の偏微分を完備化し、各座標の微分形式を左外積する。

## 規約
差座標の微分形式は二つの頂点の微分形式の差。

## 使われ方
pd de Rham 双複体の縦方向。
-/

public noncomputable section

open CategoryTheory
open SerrePositivity.DerivedCompletion
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

private def pdCoordinateVector (n : SimplexCategory) : pdCoordinates r n.len → CopyModule k r n
  | .inl t => Finsupp.single (t, 0) 1
  | .inr (t, i) => Finsupp.single (t, i.succ) 1 - Finsupp.single (t, 0) 1

private def coordinateToCopy (n : SimplexCategory) :
    (pdCoordinates r n.len →₀ k) →ₗ[k] CopyModule k r n :=
  Finsupp.linearCombination k (pdCoordinateVector k r n)

private def copyToCoordinate (n : SimplexCategory) :
    CopyModule k r n →ₗ[k] pdCoordinates r n.len →₀ k :=
  Finsupp.linearCombination k fun ji =>
    Finsupp.single (.inl ji.1) 1 +
      Fin.cases 0 (fun i => Finsupp.single (.inr (ji.1, i)) 1) ji.2

@[local simp] private theorem coordinateToCopy_single (n : SimplexCategory)
    (a : pdCoordinates r n.len) :
    coordinateToCopy k r n (Finsupp.single a 1) = pdCoordinateVector k r n a := by
  rw [coordinateToCopy, Finsupp.linearCombination_single, one_smul]

@[local simp] private theorem copyToCoordinate_zero (n : SimplexCategory) (t : Fin r) :
    copyToCoordinate k r n (Finsupp.single (t, 0) 1) = Finsupp.single (.inl t) 1 := by
  rw [copyToCoordinate, Finsupp.linearCombination_single, one_smul, Fin.cases_zero, add_zero]

@[local simp] private theorem copyToCoordinate_succ (n : SimplexCategory) (t : Fin r) (i : Fin n.len) :
    copyToCoordinate k r n (Finsupp.single (t, i.succ) 1) =
      Finsupp.single (.inl t) 1 + Finsupp.single (.inr (t, i)) 1 := by
  rw [copyToCoordinate, Finsupp.linearCombination_single, one_smul, Fin.cases_succ]

private def pdCoordinateEquiv (n : SimplexCategory) :
    (pdCoordinates r n.len →₀ k) ≃ₗ[k] CopyModule k r n :=
  LinearEquiv.ofLinearMap (f := coordinateToCopy k r n) (g := copyToCoordinate k r n)
    (by
      apply (Finsupp.basisSingleOne (R := k)).ext
      rintro ⟨t,i⟩
      change coordinateToCopy k r n (copyToCoordinate k r n (Finsupp.single (t,i) 1)) =
        Finsupp.single (t,i) 1
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [pdCoordinateVector]
      · simp [pdCoordinateVector])
    (by
      apply (Finsupp.basisSingleOne (R := k)).ext
      intro a
      change copyToCoordinate k r n (coordinateToCopy k r n (Finsupp.single a 1)) =
        Finsupp.single a 1
      rcases a with t | ⟨t,i⟩
      · simp [pdCoordinateVector]
      · simp [pdCoordinateVector])

/-- 第 0 頂点と差座標の微分形式は、頂点の微分形式の加群の基底をなす。 -/
def pdCoordinateBasis (n : SimplexCategory) :
    Module.Basis (pdCoordinates r n.len) k ((Fin r × Fin (n.len+1)) →₀ k) :=
  (Finsupp.basisSingleOne (R := k)).map (pdCoordinateEquiv k r n)

private theorem pdCoordinateBasis_apply (n : SimplexCategory) (a : pdCoordinates r n.len) :
    pdCoordinateBasis k r n a = pdCoordinateVector k r n a := by
  rw [pdCoordinateBasis, Module.Basis.map_apply]
  change coordinateToCopy k r n (Finsupp.single a 1) = _
  exact coordinateToCopy_single k r n a

private def pdCoordinateOne (n : SimplexCategory) (a : pdCoordinates r n.len) :
    ⋀[k]^1 (CopyModule k r n) :=
  (exteriorPower.oneEquiv k (CopyModule k r n)).symm (pdCoordinateVector k r n a)

private def pdPartial (n : ℕ) (a : pdCoordinates r n) :
    pdTerm p k r n →ₗ[k] pdTerm p k r n :=
  principalCompletionLinearMap k p (pdRawPartial k r n a)

private theorem pdPartial_comm (n : ℕ) (a b : pdCoordinates r n) (x : pdTerm p k r n) :
    pdPartial p k r n a (pdPartial p k r n b x) =
      pdPartial p k r n b (pdPartial p k r n a x) := by
  have h : (pdRawPartial k r n a).comp (pdRawPartial k r n b) =
      (pdRawPartial k r n b).comp (pdRawPartial k r n a) :=
    LinearMap.ext (pdRawPartial_comm k r n a b)
  have e := congrArg (principalCompletionLinearMap k p) h
  simp only [principalCompletionLinearMap_comp] at e
  exact DFunLike.congr_fun e x

/-- 固定した余単体次数での pd de Rham 微分。 -/
def pdVerticalD (n : SimplexCategory) (j : ℕ) :
    (pdRow p k r j).obj n ⟶ (pdRow p k r (j+1)).obj n :=
  ModuleCat.ofHom (∑ a : pdCoordinates r n.len, TensorProduct.map
    (pdPartial p k r n.len a) (DeRham.wedgeOne k (CopyModule k r n) j (pdCoordinateOne k r n a)))

/-- pd de Rham 微分を二回適用すると零。 -/
theorem pdVerticalD_sq (n : SimplexCategory) (j : ℕ) :
    pdVerticalD p k r n j ≫ pdVerticalD p k r n (j+1) = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f α
  change pdTerm p k r n.len at f
  change ⋀[k]^j (CopyModule k r n) at α
  change ((∑ a : pdCoordinates r n.len, TensorProduct.map
    (pdPartial p k r n.len a) (DeRham.wedgeOne k (CopyModule k r n) (j+1)
      (pdCoordinateOne k r n a))) ((∑ a : pdCoordinates r n.len, TensorProduct.map
    (pdPartial p k r n.len a) (DeRham.wedgeOne k (CopyModule k r n) j
      (pdCoordinateOne k r n a))) (f ⊗ₜ[k] α))) = 0
  simp only [LinearMap.sum_apply, TensorProduct.map_tmul, map_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (by simp) (by simp)
  · rintro ⟨a, b⟩
    dsimp
    rw [pdPartial_comm p k r n.len b a, ← TensorProduct.tmul_add]
    unfold pdCoordinateOne
    rw [DeRham.wedgeOne_swap, TensorProduct.tmul_zero]
  · rintro ⟨a, b⟩ h he
    have hab : b = a := congrArg Prod.fst he
    subst b
    apply h
    unfold pdCoordinateOne
    rw [DeRham.wedgeOne_sq, TensorProduct.tmul_zero]

/-- 第 n 列の完備 pd de Rham 余鎖複体。 -/
def pdDeRhamColumn (n : SimplexCategory) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun j => (pdRow p k r j).obj n)
    (pdVerticalD p k r n) (pdVerticalD_sq p k r n)

end SerrePositivity.BhattScholze.Prismatic
