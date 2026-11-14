module

public import SerrePositivity.EInfinity.SimplexCuts.HomogeneousTensor
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation

/-!
# 任意の複体の反復テンソルの先頭交換

Berger–Fresse §2.2.4、M14 L11 の証明分割。
元の結合子・Koszul 交換・結合子を、同じ三つの斉次元で評価する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplexCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] (K : Complex A)

/-- C324：反復テンソルの先頭交換の純粋斉次三入力評価（BF §2.2.4）。
方針：三つの構成射を順に評価して Koszul 符号を外へ出す。
規約：後続のテンソルは任意の斉次元。
使われ方：面生成元の族を先頭二位置で入れ替える公式。 -/
lemma swapFirstIso_apply (n : ℕ) (i j k t : ℤ) (ht : i + (j + k) = t)
    (x : K.X i) (y : K.X j) (z : (power K n).X k) :
    (swapFirstIso K n).hom.f t
      (ιTensorObj K (K ⊗ power K n) i (j + k) t ht
        (x ⊗ₜ[A] ιTensorObj K (power K n) j k (j + k) rfl
          (y ⊗ₜ[A] z))) =
      (i * j).negOnePow •
        ιTensorObj K (K ⊗ power K n) j (i + k) t
          (by omega) (y ⊗ₜ[A]
            ιTensorObj K (power K n) i k (i + k) rfl (x ⊗ₜ[A] z)) := by
  change (α_ K K (power K n)).hom.f t
    (((β_ K K).hom ▷ power K n).f t
      ((α_ K K (power K n)).inv.f t _)) = _
  rw [SerrePositivity.DifferentialGraded.associator_inv_apply,
    SerrePositivity.DifferentialGraded.whiskerRight_apply]
  change (α_ K K (power K n)).hom.f t
    (ιTensorObj (K ⊗ K) (power K n) (i + j) k t _
      ((signedSwap K K).hom.f (i + j)
        (ιTensorObj K K i j (i + j) rfl (x ⊗ₜ[A] y)) ⊗ₜ[A] z)) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def]
  rw [← TensorProduct.smul_tmul', map_zsmul, map_zsmul]
  congr 1
  exact associator_apply_of_sum K K (power K n)
    j i k (i + j) t (by omega) (by omega) y x z

end SerrePositivity.EInfinity.SimplexCuts
