module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns
public import Mathlib.Data.Finset.Card

/-!
模型。文献の定義との比較は後で
# 隣接する同値の削除係数の相殺

概要：Berger–Fresse §1.2.3・§1.4.4 の退化語の二つの削除係数を比較する。
方針：隣接位置で区切り順位は一つ増え、最後の出現では直前の符号が反転する。
規約：任意の有限語を扱い、全射性や非退化性を要求しない。
使われ方：退化語の符号付き削除和が零になることを証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：隣接位置の前の区切り数は一つ増える（BF §1.2.3）。
方針：新たに数える位置が前の位置自身だけであることを有限集合で比較する。
規約：前の位置が区切りであると仮定する。
使われ方：二つとも区切りである隣接同値の削除符号を比較する。 -/
lemma caesuraRank_adjacent {n l : ℕ} (u : Fin l → Fin n) (i j : Fin l)
    (hij : i.val + 1 = j.val) (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u j = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u i + 1 := by
  have he : Finset.univ.filter (fun k => k < j ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u k) =
      insert i (Finset.univ.filter (fun k => k < i ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro ⟨hkj, hc⟩
      by_cases hki : k = i
      · exact Or.inl hki
      · right
        refine ⟨?_, hc⟩
        change k.val < i.val
        have hk : k.val < j.val := hkj
        have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
        omega
    · rintro (rfl | ⟨hk, hc⟩)
      · exact ⟨by change k.val < j.val; omega, hi⟩
      · refine ⟨?_, hc⟩
        change k.val < j.val
        have hk' : k.val < i.val := hk
        omega
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank
  rw [he, Finset.card_insert_of_notMem (by simp)]

/-- 概要：隣接する同値の直前の出現は直前の位置（BF §1.2.3）。
方針：直前位置は出現集合に属し、それより大きな前の位置は存在しない。
規約：前の出現集合の非空性の証明によらない。
使われ方：最終出現の削除係数の符号反転を適用する。 -/
lemma previousOccurrences_max_adjacent {n l : ℕ} (u : Fin l → Fin n) (i j : Fin l)
    (hij : i.val + 1 = j.val) (he : u i = u j)
    (h : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u j).Nonempty) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u j).max' h = i := by
  apply le_antisymm
  · apply Finset.max'_le
    intro k hk
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    change k.val ≤ i.val
    have hk' : k.val < j.val := hk.1
    omega
  · apply Finset.le_max'
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by change i.val < j.val; omega, he⟩

/-- 概要：隣接する同値の削除係数は互いに逆（BF §1.2.3・§1.4.4）。
方針：後の位置が区切りなら交代符号、最後なら前の出現の反転を使う。
規約：単独出現の零係数の分岐は生じない。
使われ方：退化語の削除の二つの同じ項を相殺する。 -/
lemma deletionCoefficient_adjacent_eq {n l : ℕ} (u : Fin l → Fin n) (i j : Fin l)
    (hij : i.val + 1 = j.val) (he : u i = u j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u j = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u i := by
  have hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i := ⟨j, by change i.val < j.val; omega, he.symm⟩
  by_cases hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u j
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _ hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _ hj,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank_adjacent u i j hij hi, pow_succ]
    simp
  · have hm : i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u j := by
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by change i.val < j.val; omega, he⟩
    have hnon : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u j).Nonempty := ⟨i, hm⟩
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_final u j hj hnon]
    exact congrArg (fun p => -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u p)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences_max_adjacent u i j hij he hnon)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
