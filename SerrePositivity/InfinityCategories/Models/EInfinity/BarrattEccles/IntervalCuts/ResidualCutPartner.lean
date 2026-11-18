module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InverseCutValidity

/-!
模型。文献の定義との比較は後で
# 削除後だけ非零となる切断の交換相手

概要：Berger–Fresse §2.2.7 の余分な削除項について、同じ側の同色位置との交換を構成する。
方針：元の同じ側の非自明な等値対は、削除位置と一意な障害位置の対だけであることを使う。
規約：障害位置が切断点でない場合に限り、同じ元切断点を保つ相手を作る。
使われ方：余分な削除項を二項ずつ相殺する対合。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：元の同じ側の非自明な等値対は削除位置を含む（BF §2.2.7）。
方針：両位置が削除位置以外なら削除後の単射性に矛盾する。
規約：削除後の切断だけが非零でもよい。
使われ方：元の退化切断の重複を一つの位置対に限定する。 -/
lemma same_side_equal_pair_contains_deleted {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (a b : Fin (l + 1)) (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) a b)
    (hu : u a = u b) (hab : a ≠ b) : a = i ∨ b = i := by
  by_cases hai : a = i
  · exact Or.inl hai
  by_cases hbi : b = i
  · exact Or.inr hbi
  exact False.elim (hab (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_same_side_injective u i q h a b hai hbi hs hu))

/-- 概要：元の同じ側の非自明な等値対は削除位置と障害位置の対（BF §2.2.7）。
方針：一方が削除位置であることを使い、他方を障害位置の一意性で同定する。
規約：二つの位置の順序を要求しない。
使われ方：障害位置を削除し直しても切断が非零であることを示す。 -/
lemma same_side_equal_pair_is_defect_pair {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (j : Fin (l + 1)) (hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q j)
    (a b : Fin (l + 1)) (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) a b)
    (hu : u a = u b) (hab : a ≠ b) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.same_side_equal_pair_contains_deleted u i q h a b hs hu hab with ha | hb
  · subst a
    exact Or.inl ⟨rfl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cutDeletionDefect_unique u i q h b j ⟨hab.symm, hu.symm, hs⟩ hj⟩
  · subst b
    exact Or.inr ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cutDeletionDefect_unique u i q h a j ⟨hab, hu, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_symm hs⟩ hj, rfl⟩

/-- 概要：障害位置を代わりに削除して同じ切断点を残すと再び非零（BF §2.2.7）。
方針：元の同じ側の等値対は交換する二位置だけなので、障害位置の削除で全て排除される。
規約：削除後の相手の切断位置 q' を明示する。
使われ方：相殺対合の相手の非零性。 -/
lemma erase_partner_edgeNondegenerate {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (j : Fin (l + 1)) (hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q j)
    (q' : Fin l) (hq : j.succAbove q' = i.succAbove q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u j) q' := by
  have H (a b : Fin (l + 1)) (ha : a ≠ j) (hb : b ≠ j)
      (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) a b) (hu : u a = u b) : a = b := by
    by_contra hab
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.same_side_equal_pair_is_defect_pair u i q h j hj a b hs hu hab with hs | hs
    · exact hb hs.2
    · exact ha hs.1
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
  constructor
  · intro a b ha hb hab
    apply (Fin.succAbove_right_injective (p := j))
    apply H _ _ (Fin.succAbove_ne j a) (Fin.succAbove_ne j b) _ hab
    exact Or.inl ⟨by simpa only [hq] using (Fin.strictMono_succAbove j).monotone ha,
      by simpa only [hq] using (Fin.strictMono_succAbove j).monotone hb⟩
  · intro a b ha hb hab
    apply (Fin.succAbove_right_injective (p := j))
    apply H _ _ (Fin.succAbove_ne j a) (Fin.succAbove_ne j b) _ hab
    exact Or.inr ⟨by simpa only [hq] using (Fin.strictMono_succAbove j).monotone ha,
      by simpa only [hq] using (Fin.strictMono_succAbove j).monotone hb⟩

/-- 概要：障害位置が切断点でなければ相手の切断位置が一意に存在（BF §2.2.7）。
方針：切断点を新たな削除の順序単射で戻し、単射性で一意性を得る。
規約：切断点そのものが障害となる場合は含めない。
使われ方：余分な削除項の相殺対合の位置データ。 -/
lemma residual_partner_existsUnique {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (j : Fin (l + 1)) (hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q j) (hjp : j ≠ i.succAbove q) :
    ∃! q' : Fin l, j.succAbove q' = i.succAbove q ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u j) q' := by
  obtain ⟨q', hq'⟩ := Fin.exists_succAbove_eq hjp.symm
  refine ⟨q', ⟨hq', _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_partner_edgeNondegenerate u i q h j hj q' hq'⟩, ?_⟩
  intro r hr
  exact Fin.succAbove_right_injective (hr.1.trans hq'.symm)

/-- 概要：交換後の項の障害位置は元の削除位置（BF §2.2.7）。
方針：色と同じ側の条件を対称にし、元切断点の一致を使う。
規約：交換後も同じ元の退化切断に属する。
使われ方：相殺相手を二回交換すると元へ戻ることを証明する。 -/
lemma residual_partner_defect {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (j : Fin (l + 1)) (hj : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q j)
    (q' : Fin l) (hq : j.succAbove q' = i.succAbove q) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u j q' i := by
  refine ⟨hj.1.symm, hj.2.1.symm, ?_⟩
  rw [hq]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_symm hj.2.2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
