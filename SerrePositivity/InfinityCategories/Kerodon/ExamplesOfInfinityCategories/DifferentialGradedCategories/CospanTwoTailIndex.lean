module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanOneTailIndex

/-! # 末尾二点を含む未知集合の切断

概要：標準セル全体の錐頂点と最初の末尾頂点での切断と削除を計算する。
方針：先頭集合と末尾二点による頂点の分類を使い、有限集合の所属を比較する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の三角形成分の Bianchi の二寄与。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：先頭集合に末尾の二点を加えると標準セル全体になる。
方針：全頂点の三分類を使う。
規約：HTT §1.2.13。使われ方：四番目の未知集合と全体集合の同定。 -/
lemma cospanPrefix_insert_both (n : ℕ) :
    insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanVertex_cases i with hi | rfl | rfl
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- 概要：全体集合の錐頂点以下の左切断は先頭集合。
方針：先頭集合を錐頂点以下の区間と同定する。
規約：HA Proposition 1.3.1.10。使われ方：先頭残差の出現位置。 -/
lemma cospanUniv_leftCut_apex (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (· ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le]

/-- 概要：全体集合の錐頂点以上の右切断は錐頂点と末尾二点の三点集合。
方針：先頭の点が錐頂点以上なら一致し、他は末尾の二点である。
規約：HA Proposition 1.3.1.10。使われ方：三角形のホモトピー成分を取り出す。 -/
lemma cospanUniv_rightCut_apex (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n ≤ ·) =
      {_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hge
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanVertex_cases i with hi | hi | hi
    · exact Or.inl (le_antisymm ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le i).mp hi) hge)
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · rintro (rfl | rfl | rfl)
    · exact le_rfl
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).le
    · exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)).le

/-- 概要：全体集合の錐頂点より大きい頂点は末尾二点。
方針：三点の右切断から錐頂点自身を除く。
規約：HA Proposition 1.3.1.10。使われ方：錐頂点の符号の計算。 -/
lemma cospanUniv_above_apex (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < ·) =
      {_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hgt
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanVertex_cases i with hi | hi | hi
    · exact False.elim (not_le_of_gt hgt ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le i).mp hi))
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (rfl | rfl)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)

/-- 概要：全体集合の最初の末尾頂点以下の左切断は先頭とその末尾頂点。
方針：残る最後の点だけが切断の外にあることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚側の残差の出現位置。 -/
lemma cospanUniv_leftCut_firstTail (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (· ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) =
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hle
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanVertex_cases i with hi | hi | hi
    · exact Or.inr hi
    · exact Or.inl hi
    · subst i
      exact False.elim (not_le_of_gt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n) hle)
  · rintro (rfl | hi)
    · exact le_rfl
    · exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le i).mp hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).le

/-- 概要：全体集合の最初の末尾頂点以上の右切断は末尾二点。
方針：先頭集合の全ての点が最初の末尾頂点より小さいことを使う。
規約：HA Proposition 1.3.1.10。使われ方：cospan の射の次数零の成分。 -/
lemma cospanUniv_rightCut_firstTail (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n ≤ ·) =
      {_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hge
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanVertex_cases i with hi | hi | hi
    · exact False.elim (not_le_of_gt
        (lt_of_le_of_lt ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le i).mp hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)) hge)
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (rfl | rfl)
    · exact le_rfl
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n).le

/-- 概要：全体集合の最初の末尾頂点より大きい点は最後の点だけ。
方針：値の上界から最後の値を特定する。
規約：HA Proposition 1.3.1.10。使われ方：最初の末尾頂点の符号の計算。 -/
lemma cospanUniv_above_firstTail (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n < ·) = {_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hgt
    apply Fin.ext
    change i.val = n + 3
    have hi := i.isLt
    change n + 2 < i.val at hgt
    omega
  · rintro rfl
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n

/-- 概要：最初の末尾頂点を削除すると先頭集合と最後の点が残る。
方針：全体集合の末尾二点の表示で削除を計算する。
規約：HA Proposition 1.3.1.10。使われ方：D 側の残差の削除項。 -/
lemma cospanUniv_erase_firstTail (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 4))).erase (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) =
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
  rw [← cospanPrefix_insert_both, Finset.erase_insert]
  simp only [Finset.mem_insert, not_or]
  exact ⟨ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)⟩

/-- 概要：全体集合で錐頂点の符号は正一。
方針：その右側は二点なので負一の二乗を計算する。
規約：HA Proposition 1.3.1.10。使われ方：ホモトピーとの合成項の符号。 -/
lemma cospanUniv_sign_apex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (Finset.univ : Finset (Fin (n + 4))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, cospanUniv_above_apex,
    Finset.card_pair (ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)), Nat.cast_ofNat]
  decide

/-- 概要：全体集合で最初の末尾頂点の符号は負一。
方針：その右側は一点なので負一の一乗を計算する。
規約：HA Proposition 1.3.1.10。使われ方：D 側の削除項と脚側の合成項の符号。 -/
lemma cospanUniv_sign_firstTail (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (Finset.univ : Finset (Fin (n + 4))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) = -1 := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, cospanUniv_above_firstTail]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
