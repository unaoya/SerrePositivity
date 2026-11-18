module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NestedCutCoefficients
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
模型。文献の定義との比較は後で
# 元の前方出力次数と小さい色の出力次数の和

Berger–Fresse §2.2.6・§3.1、M14 L12a の C452。
同じprefixFamilyの添字を、元の指定色より小さい色へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の前方の総次数は、同じ小さい色の出力次数の和（BF §3.1）。 -/
lemma positiveNestedPrefixDegree_eq_prefixOutputDegree {m d q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + d) q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPrefixDegree u k s =
      ∑ b ∈ Finset.univ.filter (fun b : Fin (m + 1) => b < k),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) b := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPrefixDegree
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum_eq_sum]
  apply Finset.sum_bij (fun j _ => (⟨j.val, by have hj := j.isLt; have hk := k.isLt; omega⟩ :
    Fin (m + 1)))
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro j _ h _ he
    exact Fin.ext (congrArg (fun z : Fin (m + 1) => z.val) he)
  · intro j hj
    exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
