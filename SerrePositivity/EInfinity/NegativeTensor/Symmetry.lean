module

public import SerrePositivity.EInfinity.NegativeTensor.Associativity
public import SerrePositivity.EInfinity.NatTensor.Homogeneous

/-!
# 負次数テンソル比較と符号付き交換

概要：Berger–Fresse §1.1.4 の交換が自然数鎖から整数コチェインへの比較で保たれることを示す。
方針：負の各全次数の斉次包含で検査し、両方の交換符号を比較する。
規約：自然数鎖の p,q 次は整数コチェインの −p,−q 次へ移る。
使われ方：shuffle の AW 余代数適合性を実際の E の整数模型へ移す。
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

/-- 概要：テンソル比較は自然数鎖と整数コチェインの符号付き交換を保つ（BF §1.1.4）。
方針：正次数は零、負次数は斉次純テンソルで両辺の公式を計算する。
規約：符号は (−p)(−q)=pq により一致する。
使われ方：余代数のテンソルと E の整数次数の Hopf 合成。 -/
lemma comparison_symmetry (K L : ChainComplex (ModuleCat.{u} A) ℕ) :
    (comparison K L).hom ≫ (SerrePositivity.cochainTensorSymmetry (extend K) (extend L)).hom =
      extendMap (NatTensor.symmetry K L).hom ComplexShape.embeddingDownNat ≫
        (comparison L K).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (isZero_positive (HomologicalComplex.tensorObj K L) i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  apply (cancel_epi (xIso (HomologicalComplex.tensorObj K L) n).inv).1
  apply mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  let v := ιTensorObj K L p q n hpq (x ⊗ₜ[A] y)
  change (SerrePositivity.cochainTensorSymmetry (extend K) (extend L)).hom.f (-(n : ℤ))
      ((comparison K L).hom.f (-(n : ℤ)) ((xIso (HomologicalComplex.tensorObj K L) n).inv v)) =
    (comparison L K).hom.f (-(n : ℤ))
      ((extendMap (NatTensor.symmetry K L).hom ComplexShape.embeddingDownNat).f (-(n : ℤ))
        ((xIso (HomologicalComplex.tensorObj K L) n).inv v))
  simp only [extendMap_neg_inv_apply, v, NatTensor.symmetry_hom_apply_ι,
    comparison_neg_inv_apply, degreeMap_ι_tmul,
    SerrePositivity.cochainTensorSymmetry_hom_apply_ι,
    Units.smul_def, map_zsmul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  congr 1
  simp only [neg_mul_neg, ← Nat.cast_mul, Int.coe_negOnePow_natCast]

end SerrePositivity.EInfinity.NegativeTensor
