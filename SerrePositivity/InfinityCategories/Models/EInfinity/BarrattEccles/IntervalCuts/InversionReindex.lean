module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionCounts

/-!
模型。文献の定義との比較は後で
# 位置と色の順序を保つ活動集合の逆転数

概要：Berger–Fresse §2.2.4 の活動色の逆転数を順序を保つ位置写像で比較する。
方針：位置集合の像上の二重和を、単射性で元の二重和へ戻す。
規約：位置と色の厳密順序を対ごとに比較する。
使われ方：部分合成で残り活動位置だけが移る分岐の切断符号。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：活動集合の単射像で逆転対の寄与を保つと逆転数も保存（BF §2.2.4）。
方針：有限集合の像の二重和を二回添字変更する。
規約：像の外の位置や色には条件を課さない。
使われ方：合成語の活動集合を外側語へ戻す。 -/
lemma positionInversionCount_image_of_terms {n l n' l' : ℕ} (u : Fin l → Fin n)
    (v : Fin l' → Fin n') (s : Finset (Fin l)) (f : Fin l → Fin l')
    (hf : Set.InjOn f s)
    (hterm : ∀ i ∈ s, ∀ j ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm v (f i) (f j) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v (s.image f) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount
  rw [Finset.sum_image hf]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image hf]
  exact Finset.sum_congr rfl (fun j hj => hterm i hi j hj)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
