module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanUnknownIndex

/-! # cospan の未知集合の端点と濃度

概要：先頭の集合の最小元・最大元・濃度と、残差計算で使う既知集合の判定を記録する。
方針：先頭の集合を初期区間として扱い、各所属条件を有限順序集合の値へ移す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の次数と Bianchi の有限和の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：先頭の集合の最後の頂点は錐の頂点。
方針：n+2 点の最後の番号 n+1 を取る。
規約：HTT §1.2.13。使われ方：未知の先頭成分の終点と固定した錐の始点。 -/
def cospanApex (n : ℕ) : Fin (n + 4) := ⟨n + 1, by omega⟩

/-- 概要：先頭集合の所属は錐頂点以下であることと同値。
方針：有限順序集合の値の狭義・非狭義不等式を比較する。
規約：HTT §1.2.13。使われ方：左右切断で既知の集合を判定する。 -/
lemma mem_cospanPrefixFaces_iff_le {n : ℕ} (i : Fin (n + 4)) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ↔ i ≤ cospanApex n := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces]
  change i.val < n + 2 ↔ i.val ≤ n + 1
  omega

/-- 概要：先頭の集合は n+2 個の頂点を持つ。
方針：二点追加の埋め込みの単射性で像の濃度を計算する。
規約：HA Proposition 1.3.1.10。使われ方：未知成分の次数の固定。 -/
lemma card_cospanPrefixFaces (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).card = n + 2 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, Fintype.card_fin]
  · intro i j h
    exact Fin.ext (congrArg (fun z : Fin (n + 4) => z.val) h)

/-- 概要：先頭集合の最小元は零番目の頂点。
方針：零が先頭集合に属し全ての頂点以下であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：全未知成分の共通の始点。 -/
lemma cospanPrefixFaces_min (n : ℕ) (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).Nonempty) :
    (0 : Fin (n + 4)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).min' h :=
  (show IsLeast ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n : Finset _) : Set (Fin (n + 4))) 0 from
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces _).mpr (by simp), fun i _ => Fin.zero_le i⟩).unique
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).isLeast_min' h)

/-- 概要：先頭集合の最大元は錐頂点。
方針：先頭集合を錐頂点以下の区間として評価する。
規約：HA Proposition 1.3.1.10。使われ方：先頭の未知成分と脚の合成の端点。 -/
lemma cospanPrefixFaces_max (n : ℕ) (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).Nonempty) :
    cospanApex n = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).max' h :=
  (show IsGreatest ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n : Finset _) : Set (Fin (n + 4))) (cospanApex n) from
    ⟨(mem_cospanPrefixFaces_iff_le _).mpr le_rfl,
      fun i hi => (mem_cospanPrefixFaces_iff_le i).mp hi⟩).unique
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n).isGreatest_max' h)

/-- 概要：先頭の集合の最大元は零より大きい。
方針：値 n+1 の正値性。
規約：HTT §1.2.13。使われ方：Bianchi の内部点としての錐頂点。 -/
lemma cospanApex_pos (n : ℕ) : (0 : Fin (n + 4)) < cospanApex n := by
  change 0 < n + 1
  omega

/-- 概要：錐頂点は最初の末尾頂点より小さい。
方針：隣接する二つの番号を比較する。
規約：HTT §1.2.13。使われ方：三角形と未知成分の切断。 -/
lemma cospanApex_lt_firstTail (n : ℕ) : cospanApex n < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n := by
  change n + 1 < n + 2
  omega

/-- 概要：最初の末尾頂点は最後の末尾頂点より小さい。
方針：隣接する二つの番号を比較する。
規約：HTT §1.2.13。使われ方：二つの末尾頂点を含む方程式の内部点。 -/
lemma cospanFirstTail_lt_lastTail (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n := by
  change n + 2 < n + 3
  omega

/-- 概要：先頭の一点を削除した集合は既知集合になる。
方針：削除したその点を避ける選んだ面を使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi の削除項の残差を消す。 -/
lemma cospan_erase_known {n : ℕ} (I : Finset (Fin (n + 4)))
    (j : Fin (n + 4)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I.erase j := by
  intro h
  exact Finset.notMem_erase j I (h hj)

/-- 概要：錐頂点より手前で終わる左切断は既知集合。
方針：左切断が錐頂点を含まないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi の左切断の既知残差の消去。 -/
lemma cospan_leftCut_known {n : ℕ} (I : Finset (Fin (n + 4)))
    (j : Fin (n + 4)) (hj : j < cospanApex n) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I.filter (· ≤ j) := by
  intro h
  have hm := h ((mem_cospanPrefixFaces_iff_le (cospanApex n)).mpr le_rfl)
  exact not_le_of_gt hj (Finset.mem_filter.mp hm).2

/-- 概要：零より後で始まる右切断は既知集合。
方針：右切断が零番目の頂点を含まないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi の右切断の既知残差の消去。 -/
lemma cospan_rightCut_known {n : ℕ} (I : Finset (Fin (n + 4)))
    (j : Fin (n + 4)) (hj : 0 < j) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I.filter (j ≤ ·) := by
  intro h
  have hm := h ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces (0 : Fin (n + 4))).mpr (by simp))
  exact not_le_of_gt hj (Finset.mem_filter.mp hm).2

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
