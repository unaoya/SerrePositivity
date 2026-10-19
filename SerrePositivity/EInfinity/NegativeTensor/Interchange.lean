module

public import SerrePositivity.EInfinity.NegativeTensor.Symmetry
public import SerrePositivity.EInfinity.NatTensor.QuadExt

/-!
# 負次数テンソル比較と四因子交換

概要：Berger–Fresse §1.1.4 の中間二因子の交換が負次数比較で保たれることを示す。
方針：四つの斉次次数の純テンソルで両辺を評価する。
規約：全次数・二つの中間全次数に標準の負次数比較だけを使う。
使われ方：AW 余積を保つ二入力の鎖写像を整数模型へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.NegativeTensor

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct

variable {A : Type u} [CommRing A]

/-- 概要：負次数比較は四因子の中間二因子の交換を保つ（BF §1.1.4）。
方針：正次数は零、負次数は四重包含上で二つの交換の符号を同定する。
規約：余代数のテンソルに必要な実際の比較図式で述べる。
使われ方：一般 shuffle の AW 余積適合性の整数模型への移送。 -/
lemma comparison_interchange (K L M N : ChainComplex (ModuleCat.{u} A) ℕ) :
    (comparison (NatTensor.tensor K L) (NatTensor.tensor M N)).hom ≫
        HomologicalComplex.tensorHom (comparison K L).hom (comparison M N).hom ≫
        (SerrePositivity.cochainTensorShuffle (extend K) (extend L) (extend M) (extend N)).hom =
      extendMap (NatTensor.interchange K L M N).hom ComplexShape.embeddingDownNat ≫
        (comparison (NatTensor.tensor K M) (NatTensor.tensor L N)).hom ≫
        HomologicalComplex.tensorHom (comparison K M).hom (comparison L N).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (isZero_positive (NatTensor.tensor (NatTensor.tensor K L)
      (NatTensor.tensor M N)) i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  apply (cancel_epi (xIso (NatTensor.tensor (NatTensor.tensor K L) (NatTensor.tensor M N)) n).inv).1
  apply NatTensor.quad_hom_ext
  intro p q r s hpqrs
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro x y z w
  let v := NatTensor.tensorQuadι K L M N p q r s n hpqrs
    ((x ⊗ₜ[A] y) ⊗ₜ[A] (z ⊗ₜ[A] w))
  change (SerrePositivity.cochainTensorShuffle (extend K) (extend L) (extend M) (extend N)).hom.f
      (-(n : ℤ))
      ((HomologicalComplex.tensorHom (comparison K L).hom (comparison M N).hom).f (-(n : ℤ))
        ((comparison (NatTensor.tensor K L) (NatTensor.tensor M N)).hom.f (-(n : ℤ))
          ((xIso (NatTensor.tensor (NatTensor.tensor K L) (NatTensor.tensor M N)) n).inv v))) =
    (HomologicalComplex.tensorHom (comparison K M).hom (comparison L N).hom).f (-(n : ℤ))
      ((comparison (NatTensor.tensor K M) (NatTensor.tensor L N)).hom.f (-(n : ℤ))
        ((extendMap (NatTensor.interchange K L M N).hom ComplexShape.embeddingDownNat).f
          (-(n : ℤ))
          ((xIso (NatTensor.tensor (NatTensor.tensor K L) (NatTensor.tensor M N)) n).inv v)))
  simp only [extendMap_neg_inv_apply, v]
  rw [NatTensor.interchange_hom_apply_ι]
  simp only [Units.smul_def, map_zsmul, NatTensor.tensorQuadι_apply,
    comparison_neg_inv_apply, degreeMap_ι_tmul, SerrePositivity.cochainTensorMap_apply_ι]
  rw [SerrePositivity.cochainTensorQuad_apply_of_sum,
    SerrePositivity.cochainTensorShuffle_hom_apply_ι,
    SerrePositivity.cochainTensorQuad_apply_of_sum]
  congr 1
  simp only [neg_mul_neg, ← Nat.cast_mul, Int.negOnePow_def, zpow_natCast]

end SerrePositivity.EInfinity.NegativeTensor
