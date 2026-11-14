module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineRawPDFactor
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineRawPDFactor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRawComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineAffineDivision
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 未完備結晶模型の高次 δ 座標の分離

## 概要
分冪模型の台環から正の反復 δ 座標の多項式因子を分離する。

## 方針
階乗部分環の表示を用い、テンソル積の因子を入れ替える。

## 規約
分冪因子は頂点差だけに置く。

## 使われ方
結晶模型の余分な座標の収縮。
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct
open Algebra.TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

section Tensor

variable (k : Type u) [CommRing k] (r n : ℕ)

local notation "M₀" => MvPolynomial (Fin r) k
local notation "M₁" => MvPolynomial (CrystallineExtraIndex r n) k
local notation "M₂" => MvPolynomial (Fin r ⊕ CrystallineExtraIndex r n) k
local notation "G" => DividedPowerAlgebra k ((Fin r × Fin n) →₀ k)

private def rearrangeTensor :
    M₂ ⊗[k] DividedPowerAlgebra k (ULift.{u} (Fin r × Fin n) →₀ k) ≃ₐ[k]
      pdRaw k r n ⊗[k] M₁ :=
  (Algebra.TensorProduct.congr (MvPolynomial.tensorEquivSum k (Fin r) _ k).symm
    (DividedPowerAlgebra.mapEquiv (Finsupp.domLCongr (R := k) Equiv.ulift))).trans
    ((Algebra.TensorProduct.assoc k k k M₀ M₁ G).trans
      ((Algebra.TensorProduct.congr ((AlgEquiv.refl : M₀ ≃ₐ[k] M₀))
        (Algebra.TensorProduct.comm k M₁ G)).trans
          (Algebra.TensorProduct.assoc k k k M₀ G M₁).symm))

private theorem rearrangeTensor_tmul (x : M₀) (y : M₁)
    (g : DividedPowerAlgebra k (ULift.{u} (Fin r × Fin n) →₀ k)) :
    rearrangeTensor k r n ((MvPolynomial.tensorEquivSum k (Fin r) _ k (x ⊗ₜ[k] y)) ⊗ₜ[k] g) =
      (x ⊗ₜ[k] DividedPowerAlgebra.mapEquiv
        (Finsupp.domLCongr (R := k) Equiv.ulift) g) ⊗ₜ[k] y := by
  simp [rearrangeTensor]

end Tensor

variable (p : ℕ) [Fact p.Prime] (r n : ℕ)

/-- 未完備の結晶側模型を、未完備の pd 模型と高次座標のテンソル積で表示する。 -/
def crystallineRawPDSplit :
    let R := RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n)
    let E := relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure
    DeltaAdjoinDivision E (p : R) (crystallineRawPDDifference.{u} p r n) ≃+*
      pdRaw (crystallineBase.{u} p) r n ⊗[crystallineBase.{u} p]
        MvPolynomial (CrystallineExtraIndex r n) (crystallineBase.{u} p) :=
  (crystallineRawPDFactor.{u} p r n).trans
    (rearrangeTensor (crystallineBase.{u} p) r n).toRingEquiv

private abbrev rawJ (p : ℕ) [Fact p.Prime] (r n : ℕ) :=
  deltaAdjoinDivisionMap
    (relativeFreeDeltaStructure (AffineIndex.{u} r n) (crystallineBasePrism.{u} p).deltaStructure)
    (p : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r n))
    (crystallineRawPDDifference.{u} p r n)

private theorem rawPDSplit_base (j : Fin r) :
    crystallineRawPDSplit.{u} p r n (rawJ.{u} p r n (MvPolynomial.X (⟨(j,0)⟩,0))) =
      ((MvPolynomial.X j) ⊗ₜ[crystallineBase.{u} p] 1) ⊗ₜ[crystallineBase.{u} p] 1 := by
  have h := rawPDFactor_coefficient.{u} p r n (MvPolynomial.X (⟨(j,0)⟩,0))
  rw [crystallineRawCoordinateEquiv_base] at h
  have h₁ := (rawFactorialTensorEquiv.{u} p r n).injective
    (h.trans (rawFactorialTensor_left.{u} p r n (MvPolynomial.X (.inl j))).symm)
  let k := crystallineBase.{u} p
  refine (congrArg (rearrangeTensor k r n) h₁).trans ?_
  exact (congrArg (fun x => rearrangeTensor k r n (x ⊗ₜ[k] 1))
      (MvPolynomial.tensorEquivSum_X_tmul_one (R := k) (S := k)
        (ι := CrystallineExtraIndex r n) j).symm).trans (by
    rw [rearrangeTensor_tmul, map_one]
    rfl)

private theorem rawPDSplit_extra (j : Fin r) (i : Fin (n + 1)) (a : ℕ) :
    crystallineRawPDSplit.{u} p r n (rawJ.{u} p r n (MvPolynomial.X (⟨(j,i)⟩,a + 1))) =
      1 ⊗ₜ[crystallineBase.{u} p] MvPolynomial.X ((j,a),i) := by
  have h := rawPDFactor_coefficient.{u} p r n (MvPolynomial.X (⟨(j,i)⟩,a + 1))
  rw [crystallineRawCoordinateEquiv_extra] at h
  have h₁ := (rawFactorialTensorEquiv.{u} p r n).injective
    (h.trans (rawFactorialTensor_left.{u} p r n (MvPolynomial.X (.inr ((j,a),i)))).symm)
  let k := crystallineBase.{u} p
  refine (congrArg (rearrangeTensor k r n) h₁).trans ?_
  exact (congrArg (fun x => rearrangeTensor k r n (x ⊗ₜ[k] 1))
      (MvPolynomial.tensorEquivSum_one_tmul_X (R := k) (S := k)
        (σ := Fin r) ((j,a),i)).symm).trans (by
    rw [rearrangeTensor_tmul, map_one, Algebra.TensorProduct.one_def]
    rfl)

private theorem rawPDSplit_diff (t : ULift.{u} (Fin r × Fin n)) :
    crystallineRawPDSplit.{u} p r n (rawJ.{u} p r n (rawDifference.{u} p r n t)) =
      (1 ⊗ₜ[crystallineBase.{u} p] DividedPowerAlgebra.dp (crystallineBase.{u} p) 1
        (Finsupp.single t.down 1)) ⊗ₜ[crystallineBase.{u} p] 1 := by
  have h := rawPDFactor_coefficient.{u} p r n (rawDifference.{u} p r n t)
  rw [show crystallineRawCoordinateEquiv (k := crystallineBase.{u} p) r n
      (rawDifference.{u} p r n t) = MvPolynomial.X t from crystallineRawCoordinateEquiv_diff r n t] at h
  have h₁ := (rawFactorialTensorEquiv.{u} p r n).injective
    (h.trans (rawFactorialTensor_diff.{u} p r n t).symm)
  let k := crystallineBase.{u} p
  refine (congrArg (rearrangeTensor k r n) h₁).trans ?_
  let dp := DividedPowerAlgebra.dp k 1 (Finsupp.single t (1 : k))
  exact (congrArg (fun x => rearrangeTensor k r n (x ⊗ₜ[k] dp))
      (map_one (MvPolynomial.tensorEquivSum k (Fin r) (CrystallineExtraIndex r n) k)).symm).trans
    (by
      rw [Algebra.TensorProduct.one_def, rearrangeTensor_tmul]
      simp [dp, DividedPowerAlgebra.mapEquiv, DividedPowerAlgebra.map_apply_dp]
      rfl)

set_option maxHeartbeats 800000 in
-- 二重のテンソル積に頂点差と基点を代入する。
private theorem rawPDSplit_copy (m : SimplexCategory) (j : Fin r) (i : Fin (m.len + 1)) :
    crystallineRawPDSplit.{u} p r m.len (rawJ.{u} p r m.len (MvPolynomial.X (⟨(j,i)⟩,0))) =
      copy (crystallineBase.{u} p) r m j i ⊗ₜ[crystallineBase.{u} p] 1 := by
  refine Fin.cases ?_ (fun d => ?_) i
  · rw [rawPDSplit_base]
    simp [copy, vertexDiff, baseVar]
  · have h : (MvPolynomial.X (⟨(j,d.succ)⟩,0) :
        RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len)) =
        rawDifference.{u} p r m.len ⟨(j,d)⟩ + MvPolynomial.X (⟨(j,0)⟩,0) := by
      rw [rawDifference, sub_add_cancel]
    let k := crystallineBase.{u} p
    let B := RelativeFreeDeltaRing (R := k) (AffineIndex.{u} r m.len)
    let W := MvPolynomial (CrystallineExtraIndex r m.len) k
    let T := pdRaw k r m.len ⊗[k] W
    let f : B →+* T := (crystallineRawPDSplit.{u} p r m.len).toRingHom.comp (rawJ.{u} p r m.len)
    let v : pdRaw k r m.len := (1 ⊗ₜ[k] DividedPowerAlgebra.dp k 1 (Finsupp.single (j,d) 1))
    let b : pdRaw k r m.len := (MvPolynomial.X j ⊗ₜ[k] 1)
    let z : B := rawDifference.{u} p r m.len ⟨(j,d)⟩
    let x₀ : B := MvPolynomial.X (⟨(j,0)⟩,0)
    have hb : v + b = copy k r m j d.succ := add_comm _ _
    have hv : f z = v ⊗ₜ[k] (1 : W) := rawPDSplit_diff p r m.len ⟨(j,d)⟩
    have hbase : f x₀ = b ⊗ₜ[k] (1 : W) := rawPDSplit_base p r m.len j
    have h' : f (z + x₀) = f z + f x₀ := f.map_add z x₀
    calc
      _ = f (z + x₀) := congrArg f h
      _ = f z + f x₀ := h'
      _ = (v ⊗ₜ[k] 1) + (b ⊗ₜ[k] 1) := congrArg₂ (fun x y : T => x + y) hv hbase
      _ = (v + b) ⊗ₜ[k] 1 := (TensorProduct.add_tmul v b (1 : W)).symm
      _ = _ := congrArg (fun x => x ⊗ₜ[k] (1 : W)) hb

private theorem rawPDSplit_C (x : crystallineBase.{u} p) :
    crystallineRawPDSplit.{u} p r n (rawJ.{u} p r n (MvPolynomial.C x)) =
      (MvPolynomial.C x ⊗ₜ[crystallineBase.{u} p] 1) ⊗ₜ[crystallineBase.{u} p] 1 := by
  have h := rawPDFactor_coefficient.{u} p r n (MvPolynomial.C x)
  rw [crystallineRawCoordinateEquiv_C] at h
  have h₁ := (rawFactorialTensorEquiv.{u} p r n).injective
    (h.trans (rawFactorialTensor_left.{u} p r n (MvPolynomial.C x)).symm)
  let k := crystallineBase.{u} p
  refine (congrArg (rearrangeTensor k r n) h₁).trans ?_
  exact (congrArg (fun y => rearrangeTensor k r n (y ⊗ₜ[k] 1))
      (MvPolynomial.tensorEquivSum_C_tmul_one (R := k) (S := k)
        (σ := Fin r) (ι := CrystallineExtraIndex r n) x).symm).trans (by
    rw [rearrangeTensor_tmul, map_one]
    rfl)

end SerrePositivity.BhattScholze.Prismatic
