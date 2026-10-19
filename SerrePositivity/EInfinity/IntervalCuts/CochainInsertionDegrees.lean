module

public import SerrePositivity.EInfinity.IntervalCuts.CochainInsertionSums

/-!
# 指定整数次数での内側余作用の代入

概要：Berger–Fresse §3.1 の内側余代入の有限和を任意の同じ全次数表示へ移す。
方針：元の面族の全次数と前後ブロックの次数の一致を使う。
規約：元の族の次数の証明と二入力の全次数を明示する。
使われ方：外側余演算の出力次数を変えず、内側余代入を評価する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：任意の同じ整数次数表示で内側余代入の切断和を評価する（BF §3.1）。
方針：元の族の全次数を前後ブロックの次数へ書き換えて既存の評価を適用する。
規約：出力次数の表示は外側作用のものを保持する。
使われ方：外側切断和の各項を内側切断和へ展開する。 -/
lemma tensorCoInsertionAction_cochain_basis_sum_at {m n e : ℕ} (v : BasisWord n e)
    (i : Fin (m + 1)) (f : Fin (m + 1) → Simplex) (b z : ℤ)
    (hb : -(tupleDegree (m + 1) f : ℤ) = b) (hz : -(e : ℤ) + b = z) :
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f z
      (ιTensorObj (complex A n) (power (interval A) (m + 1)) (-(e : ℤ)) b z hz
        ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A]
          tensorVectorAt A (m + 1) f b hb)) =
      (-(e : ℤ) * -(prefixDegree (m + 1) f i : ℤ)).negOnePow •
        ∑ a : FaceCut v (f i), a.coefficient •
          tensorVectorAt A (m + n) (insertionFamily f a.output i) z (by
            rw [tupleDegree_insertionFamily]
            have := a.output_tupleDegree
            have := tupleDegree_family_blocks f i
            omega) := by
  have hb' : b = -(tupleDegree i.val (prefixFamily f i) : ℤ) +
      (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ)) := by
    have := tupleDegree_family_blocks f i
    omega
  cases hb'
  exact tensorCoInsertionAction_cochain_basis_sum A v i f z hz

end SerrePositivity.EInfinity.IntervalCuts
