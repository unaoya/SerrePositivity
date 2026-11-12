module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportPairing

/-!
概要：edgewise の領域外の頂点集合の pairing に使う左の最初の添字と順位。
方針：最小の左添字を選び、その反対順序と頂点数の辞書式順位で他の面を下げる。
規約：順位は頂点集合についての有限な計算であり、単体的 pairing の正則性への入力。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、反転比較のホーン接合の停止性。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：頂点集合に含まれる左頂点の添字集合。
方針：全添字を左頂点の所属条件で絞る。
規約：添字は左因子の反転前の番号。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、pairing に用いる最初の左頂点の選択。 -/
def edgewiseLeftSupport (n : ℕ) (S : Finset (Fin (n + n + 1 + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i ∈ S)

/-- 概要：延長領域の外の頂点集合は左頂点を少なくとも一つ含む。
方針：右半分に含まれない頂点を取り、その番号を反転して左の添字にする。
規約：空集合は領域内なので除かれる。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の添字選択の非空性。 -/
lemma edgewiseLeftSupport_nonempty {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (h : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) :
    (edgewiseLeftSupport n S).Nonempty := by
  classical
  have hR : ¬ S ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices n := fun hR ↦ h (Or.inl hR)
  obtain ⟨v, hv, hn⟩ := Finset.not_subset.mp hR
  have hvn : v.val ≤ n := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt] using hn
  let i : Fin (n + 1) := ⟨n - v.val, by omega⟩
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i = v := by
    apply Fin.ext
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex, i]
    omega
  refine ⟨i, ?_⟩
  simp only [edgewiseLeftSupport, Finset.mem_filter, Finset.mem_univ, true_and, hi]
  exact hv

/-- 概要：延長領域の外の頂点集合の最小の左添字。
方針：非空な左添字集合の最小元を取る。
規約：領域外の証明の選択には依存しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、挿入・削除する右頂点の指定。 -/
def edgewiseSupportPivot {n : ℕ} (S : Finset (Fin (n + n + 1 + 1)))
    (h : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) : Fin (n + 1) :=
  (edgewiseLeftSupport n S).min' (edgewiseLeftSupport_nonempty S h)

/-- 概要：選んだ最小添字の左頂点は元の頂点集合に含まれる。
方針：有限集合の最小元の所属と左添字集合の定義を使う。
規約：S は延長領域外。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、対応する右頂点の挿入の適用条件。 -/
lemma edgewiseSupportPivot_mem {n : ℕ} (S : Finset (Fin (n + n + 1 + 1)))
    (h : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n (edgewiseSupportPivot S h) ∈ S := by
  have hi := Finset.min'_mem (edgewiseLeftSupport n S) (edgewiseLeftSupport_nonempty S h)
  exact (Finset.mem_filter.mp hi).2

/-- 概要：選んだ左添字は元の集合の全ての左添字以下。
方針：左添字集合の最小元の普遍性を使う。
規約：i の左頂点の所属を明示する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、他の面での添字の単調性。 -/
lemma edgewiseSupportPivot_le {n : ℕ} (S : Finset (Fin (n + n + 1 + 1)))
    (h : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) (i : Fin (n + 1))
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i ∈ S) : edgewiseSupportPivot S h ≤ i := by
  exact Finset.min'_le (edgewiseLeftSupport n S) i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

/-- 概要：対の大きい方の単体の面を取ると、最小の左添字は減らない。
方針：挿入した右頂点は左頂点と異なるので、面の最小の左頂点は元の集合にも含まれる。
規約：S と T はともに延長領域外の頂点集合。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の順位の第一成分の比較。 -/
lemma edgewiseSupportPivot_le_of_subset_pair {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) (hT : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n T)
    (hST : S ⊆ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (edgewiseSupportPivot T hT)) T) :
    edgewiseSupportPivot T hT ≤ edgewiseSupportPivot S hS := by
  apply edgewiseSupportPivot_le T hT
  have hi := hST (edgewiseSupportPivot_mem S hS)
  rcases Finset.mem_insert.mp hi with hi | hi
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex_ne_right n _ _ hi).elim
  · exact hi

/-- 概要：左添字が変わらない別の対の面では、頂点数が厳密に減る。
方針：面 S が対応する右頂点を欠くことから挿入前の T に含まれ、相異性から真部分集合となる。
規約：S は pairing の小さい方に対応する条件を満たす。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の順位の第二成分の減少。 -/
lemma edgewiseSupport_card_lt_of_pivot_eq {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) (hT : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n T)
    (hST : S ⊆ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (edgewiseSupportPivot T hT)) T)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (edgewiseSupportPivot S hS) ∉ S)
    (hP : edgewiseSupportPivot S hS = edgewiseSupportPivot T hT) (hne : S ≠ T) :
    S.card < T.card := by
  have hsub : S ⊆ T := by
    intro v hv
    rcases Finset.mem_insert.mp (hST hv) with he | he
    · rw [he, ← hP] at hv
      exact (hR hv).elim
    · exact he
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-- 概要：pairing の別の面は、反転した左添字と頂点数の辞書式順位を厳密に下げる。
方針：添字が大きくなる場合と、添字が等しく頂点数が減る場合に分ける。
規約：順位の第一成分は n-pivot、第二成分は頂点数。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、ホーン接合の正則性の有限な停止性証明。 -/
lemma edgewiseSupport_rank_lt {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) (hT : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n T)
    (hST : S ⊆ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (edgewiseSupportPivot T hT)) T)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n (edgewiseSupportPivot S hS) ∉ S) (hne : S ≠ T) :
    Prod.Lex (· < ·) (· < ·)
      (n - (edgewiseSupportPivot S hS).val, S.card)
      (n - (edgewiseSupportPivot T hT).val, T.card) := by
  by_cases hP : edgewiseSupportPivot S hS = edgewiseSupportPivot T hT
  · rw [hP]
    exact Prod.Lex.right _ (edgewiseSupport_card_lt_of_pivot_eq S T hS hT hST hR hP hne)
  · have hle := edgewiseSupportPivot_le_of_subset_pair S T hS hT hST
    apply Prod.Lex.left
    have hSlt := (edgewiseSupportPivot S hS).isLt
    have hTlt := (edgewiseSupportPivot T hT).isLt
    have hne' : (edgewiseSupportPivot S hS).val ≠ (edgewiseSupportPivot T hT).val :=
      fun he ↦ hP (Fin.ext he)
    change (edgewiseSupportPivot T hT).val ≤ (edgewiseSupportPivot S hS).val at hle
    omega

/-- 概要：右頂点の挿入は左添字の集合を変えない。
方針：左右の頂点が異なることを有限集合の挿入の所属条件へ適用する。
規約：挿入する添字 i は任意。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing で選ぶ添字の保存。 -/
lemma edgewiseLeftSupport_insert_right {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1)) :
    edgewiseLeftSupport n (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) S) = edgewiseLeftSupport n S := by
  ext j
  simp only [edgewiseLeftSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex_ne_right, false_or]

/-- 概要：右頂点の削除は左添字の集合を変えない。
方針：左右の頂点が異なることを有限集合の削除の所属条件へ適用する。
規約：削除する添字 i は任意。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の逆操作での添字の保存。 -/
lemma edgewiseLeftSupport_erase_right {n : ℕ}
    (S : Finset (Fin (n + n + 1 + 1))) (i : Fin (n + 1)) :
    edgewiseLeftSupport n (S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i)) = edgewiseLeftSupport n S := by
  ext j
  simp only [edgewiseLeftSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase]
  exact and_iff_right (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex_ne_right n j i)

/-- 概要：左添字集合が等しい二つの領域外の頂点集合は同じ最小添字を選ぶ。
方針：最小元の定義を使い、非空性の証明の違いを証明無関連性で消す。
規約：S と T の右側の頂点は独立に変えてよい。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、挿入と削除が互いに逆になることの確認。 -/
lemma edgewiseSupportPivot_eq_of_leftSupport_eq {n : ℕ}
    (S T : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n S) (hT : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n T)
    (hST : edgewiseLeftSupport n S = edgewiseLeftSupport n T) :
    edgewiseSupportPivot S hS = edgewiseSupportPivot T hT := by
  unfold edgewiseSupportPivot
  simp only [hST]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
