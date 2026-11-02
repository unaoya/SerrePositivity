module

public import SerrePositivity.EInfinity.IntervalCuts.TensorDegreeTransport
public import SerrePositivity.EInfinity.IntervalCuts.CochainUnit
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation

/-!
# 区間テンソルの先頭二因子の Koszul 交換

概要：Berger–Fresse §2.2.4 の出力交換符号を実際の複体の対称性で評価する。
方針：結合子の逆、二因子の braiding、結合子を純粋斉次テンソルで計算する。
規約：符号は整数次数の積の negOnePow。
使われ方：区間切断余演算の隣接互換に対する等変性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：反復区間テンソルの先頭交換の純粋斉次三入力評価（BF §2.2.4）。
方針：三つの構成射を順に評価して Koszul 符号を外へ出す。
規約：後続のテンソルは任意の斉次元。
使われ方：面生成元の族を先頭二位置で入れ替える公式。 -/
lemma swapFirstIso_apply (n : ℕ) (i j k t : ℤ) (ht : i + (j + k) = t)
    (x : (interval A).X i) (y : (interval A).X j) (z : (power (interval A) n).X k) :
    (swapFirstIso (interval A) n).hom.f t
      (ιTensorObj (interval A) ((interval A) ⊗ power (interval A) n) i (j + k) t ht
        (x ⊗ₜ[A] ιTensorObj (interval A) (power (interval A) n) j k (j + k) rfl
          (y ⊗ₜ[A] z))) =
      (i * j).negOnePow •
        ιTensorObj (interval A) ((interval A) ⊗ power (interval A) n) j (i + k) t
          (by omega) (y ⊗ₜ[A]
            ιTensorObj (interval A) (power (interval A) n) i k (i + k) rfl (x ⊗ₜ[A] z)) := by
  change (α_ (interval A) (interval A) (power (interval A) n)).hom.f t
    (((β_ (interval A) (interval A)).hom ▷ power (interval A) n).f t
      ((α_ (interval A) (interval A) (power (interval A) n)).inv.f t _)) = _
  rw [SerrePositivity.DifferentialGraded.associator_inv_apply,
    SerrePositivity.DifferentialGraded.whiskerRight_apply]
  change (α_ (interval A) (interval A) (power (interval A) n)).hom.f t
    (ιTensorObj ((interval A) ⊗ interval A) (power (interval A) n) (i + j) k t _
      ((signedSwap (interval A) (interval A)).hom.f (i + j)
        (ιTensorObj (interval A) (interval A) i j (i + j) rfl (x ⊗ₜ[A] y)) ⊗ₜ[A] z)) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def]
  rw [← TensorProduct.smul_tmul', map_zsmul, map_zsmul]
  congr 1
  exact associator_apply_of_sum (interval A) (interval A) (power (interval A) n)
    j i k (i + j) t (by omega) (by omega) y x z

end SerrePositivity.EInfinity.IntervalCuts
