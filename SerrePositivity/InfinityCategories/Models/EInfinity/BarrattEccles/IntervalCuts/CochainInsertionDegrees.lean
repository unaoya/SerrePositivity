module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CochainInsertionSums

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：任意の同じ整数次数表示で内側余代入の切断和を評価する（BF §3.1）。
方針：元の族の全次数を前後ブロックの次数へ書き換えて既存の評価を適用する。
規約：出力次数の表示は外側作用のものを保持する。
使われ方：外側切断和の各項を内側切断和へ展開する。 -/
lemma tensorCoInsertionAction_cochain_basis_sum_at {m n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (i : Fin (m + 1)) (f : Fin (m + 1) → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (b z : ℤ)
    (hb : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (m + 1) f : ℤ) = b) (hz : -(e : ℤ) + b = z) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) m n i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n)).f z
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (m + 1)) (-(e : ℤ)) b z hz
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)) ⊗ₜ[A]
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + 1) f b hb)) =
      (-(e : ℤ) * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (m + 1) f i : ℤ)).negOnePow •
        ∑ a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (f i), a.coefficient •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily f a.output i) z (by
            rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_insertionFamily]
            have := a.output_tupleDegree
            have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_family_blocks f i
            omega) := by
  have hb' : b = -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixFamily f i) : ℤ) +
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f i) : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (m - i.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.suffixFamily f i) : ℤ)) := by
    have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_family_blocks f i
    omega
  cases hb'
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorCoInsertionAction_cochain_basis_sum A v i f z hz

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
