module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTensorElementCalculus
/-!
概要：二つの複体の境界 cochain から、同じ tensor 境界の比較 cochain を構成する。
方針：同じ斉次 tensor の微分を端点次数0・1で評価して、実境界式へ接続する。
規約：Small 性や平坦性は不要。使われ方：二つの実 dg nerve 単体の tensor 構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R]
/-- 指定した二原始元の tensor 和は、同じ二閉射の tensor の差を境界に持つ。 -/
lemma complexTensorBoundary (P Q : Complex R)
    (f₀ f₁ : P.X 0) (g₀ g₁ : Q.X 0) (h : P.X (-1)) (k : Q.X (-1))
    (hf : P.d 0 1 f₀ = 0) (hg : Q.d 0 1 g₁ = 0)
    (hh : P.d (-1) 0 h = f₁ - f₀) (hk : Q.d (-1) 0 k = g₁ - g₀) :
    (SerrePositivity.cochainTensor P Q).d (-1) 0
      (ιTensorObj P Q (-1) 0 (-1) (by decide) (h ⊗ₜ[R] g₁) +
        ιTensorObj P Q 0 (-1) (-1) (by decide) (f₀ ⊗ₜ[R] k)) =
    ιTensorObj P Q 0 0 0 (by decide) (f₁ ⊗ₜ[R] g₁) -
      ιTensorObj P Q 0 0 0 (by decide) (f₀ ⊗ₜ[R] g₀) := by
  have h₁ := SerrePositivity.cochainTensor_d_apply_ι P Q (-1) 0 (-1) (by decide) h g₁
  have h₂ := SerrePositivity.cochainTensor_d_apply_ι P Q 0 (-1) (-1) (by decide) f₀ k
  have h₁' : (SerrePositivity.cochainTensor P Q).d (-1) 0
      (ιTensorObj P Q (-1) 0 (-1) (by decide) (h ⊗ₜ[R] g₁)) =
    ιTensorObj P Q 0 0 0 (by decide) (P.d (-1) 0 h ⊗ₜ[R] g₁) +
      (-1 : ℤ).negOnePow • ιTensorObj P Q (-1) 1 0 (by decide) (h ⊗ₜ[R] Q.d 0 1 g₁) := by
    simpa only using! h₁
  have h₂' : (SerrePositivity.cochainTensor P Q).d (-1) 0
      (ιTensorObj P Q 0 (-1) (-1) (by decide) (f₀ ⊗ₜ[R] k)) =
    ιTensorObj P Q 1 (-1) 0 (by decide) (P.d 0 1 f₀ ⊗ₜ[R] k) +
      (0 : ℤ).negOnePow • ιTensorObj P Q 0 0 0 (by decide) (f₀ ⊗ₜ[R] Q.d (-1) 0 k) := by
    simpa only using! h₂
  rw [map_add, h₁', h₂', hh, hk, hf, hg]
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero,
    smul_zero, add_zero, zero_add, Int.negOnePow_zero, one_smul,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub, map_sub]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
