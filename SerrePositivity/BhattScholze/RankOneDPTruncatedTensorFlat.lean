module

public import SerrePositivity.BhattScholze.RankOneDPTruncatedFree
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # 切断多項式作用による分冪テンソルの相対平坦性 -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} {A : Type u} [CommRing A]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "G₀" => DividedPowerAlgebra A A

/-- 実切断多項式作用での分冪テンソルは、元のA作用を保ってMの可算直和と同値。 -/
def rankOneDPTruncatedTensorEquiv (M : Type v) [AddCommGroup M]
    [Module C₀ M] [Module A M] [IsScalarTower A C₀ M] :
    letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
    (G₀ ⊗[C₀] M) ≃ₗ[A] (ℕ →₀ M) := by
  letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
  letI : IsScalarTower A C₀ G₀ := rankOneDPTruncated_isScalarTower hprime.pos hp
  exact ((TensorProduct.congr (rankOneDPTruncatedEquiv hprime hp).symm
      (LinearEquiv.refl C₀ M)).trans
    ((TensorProduct.finsuppLeft C₀ C₀ C₀ M ℕ).trans
      (Finsupp.mapRange.linearEquiv (TensorProduct.lid C₀ M)))).restrictScalars A

/-- 指定された自由基底元との純テンソルは、対応する一項係数族へ写る。 -/
theorem rankOneDPTruncatedTensorEquiv_generator (M : Type v) [AddCommGroup M]
    [Module C₀ M] [Module A M] [IsScalarTower A C₀ M] (k : ℕ) (m : M) :
    letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
    rankOneDPTruncatedTensorEquiv hprime hp M
      (DividedPowerAlgebra.dp A (p * k) (1 : A) ⊗ₜ[C₀] m) = Finsupp.single k m := by
  let : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
  let : IsScalarTower A C₀ G₀ := rankOneDPTruncated_isScalarTower hprime.pos hp
  have he : (rankOneDPTruncatedEquiv hprime hp).symm
      (DividedPowerAlgebra.dp A (p * k) (1 : A)) = Finsupp.single k (1 : C₀) := by
    apply (rankOneDPTruncatedEquiv hprime hp).injective
    rw [LinearEquiv.apply_symm_apply, rankOneDPTruncatedEquiv_single, one_smul]
  simp only [rankOneDPTruncatedTensorEquiv, LinearEquiv.restrictScalars_apply,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, he]
  ext i
  simp only [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply,
    TensorProduct.finsuppLeft_apply_tmul_apply, TensorProduct.lid_tmul]
  change (Finsupp.single k (1 : C₀)) i • m = (Finsupp.single k m) i
  by_cases hi : i = k
  · subst i
    simp only [Finsupp.single_eq_same, one_smul]
  · simp only [Finsupp.single_eq_of_ne hi, zero_smul]

/-- 切断多項式作用による実分冪テンソルは、元の係数環上の平坦性を保存・反映する。 -/
theorem rankOneDPTruncatedTensor_flat_iff (M : Type v) [AddCommGroup M]
    [Module C₀ M] [Module A M] [IsScalarTower A C₀ M] :
    letI : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
    Module.Flat A (G₀ ⊗[C₀] M) ↔ Module.Flat A M := by
  let := rankOneDPTruncatedAlgebra hprime.pos hp
  have hf : Module.Flat A (ℕ →₀ M) ↔ Module.Flat A M := by
    rw [Module.Flat.equiv_iff (finsuppLEquivDirectSum A M ℕ), Module.Flat.directSum_iff]
    simp only [forall_const]
  exact (Module.Flat.equiv_iff (rankOneDPTruncatedTensorEquiv hprime hp M)).trans hf

end SerrePositivity.BhattScholze
