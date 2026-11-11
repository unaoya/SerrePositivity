module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanIndexGeometry
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Signs

/-! # 末尾一点を加えた未知集合の切断

概要：先頭集合に末尾の一点を加えると、錐頂点での切断は先頭集合と二点集合になる。
方針：初期区間の所属条件で有限集合の外延性を示す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：δr_B・δr_C・δr_D の残差恒等式。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：錐頂点より後の点は先頭集合に属さない。
方針：先頭集合の初期区間による判定を使う。
規約：HTT §1.2.13。使われ方：末尾一点追加の濃度の計算。 -/
lemma cospanTail_notMem_prefix {n : ℕ} (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    b ∉ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le]
  exact not_le_of_gt hb

/-- 概要：末尾の一点を加えた集合は n+3 個の頂点を持つ。
方針：新しい点が先頭集合に属さないことと先頭集合の濃度を使う。
規約：HA Proposition 1.3.1.10。使われ方：脚を含む未知成分の次数。 -/
lemma card_cospanPrefix_insert {n : ℕ} (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).card = n + 3 := by
  rw [Finset.card_insert_of_notMem (cospanTail_notMem_prefix b hb), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]

/-- 概要：末尾一点追加後も最小元は零。
方針：零が集合に属し、全ての頂点以下であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi の共通の始点。 -/
lemma cospanPrefix_insert_min {n : ℕ} (b : Fin (n + 4))
    (h : (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).Nonempty) :
    (0 : Fin (n + 4)) = (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).min' h :=
  (show IsLeast ((insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) : Finset _) : Set (Fin (n + 4))) 0 from
    ⟨Finset.mem_insert_of_mem ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces _).mpr (by simp)),
      fun i _ => Fin.zero_le i⟩).unique ((insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).isLeast_min' h)

/-- 概要：末尾一点追加後の最大元は追加した点。
方針：先頭の全ての点が錐頂点以下であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚の方程式の終点。 -/
lemma cospanPrefix_insert_max {n : ℕ} (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b)
    (h : (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).Nonempty) :
    b = (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).max' h := by
  apply IsGreatest.unique _ ((insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).isGreatest_max' h)
  refine ⟨Finset.mem_insert_self _ _, ?_⟩
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact le_rfl
  · exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le i).mp hi).trans hb.le

/-- 概要：末尾一点追加後の錐頂点以下の左切断は先頭集合。
方針：追加した点が錐頂点より後にあることを使う。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi に残る先頭の残差の特定。 -/
lemma cospanPrefix_insert_leftCut {n : ℕ} (b : Fin (n + 4)) :
    (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).filter (· ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le]
  constructor
  · exact And.right
  · intro hi
    exact ⟨Or.inr hi, hi⟩

/-- 概要：末尾一点追加後の錐頂点以上の右切断は錐頂点と末尾の二点集合。
方針：先頭集合の点が錐頂点以上ならその頂点自身に等しい。
規約：HA Proposition 1.3.1.10。使われ方：残差に合成する閉次数零の脚の特定。 -/
lemma cospanPrefix_insert_rightCut {n : ℕ} (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n ≤ ·) = {_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n, b} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le]
  constructor
  · rintro ⟨rfl | hi, hge⟩
    · exact Or.inr rfl
    · exact Or.inl (le_antisymm hi hge)
  · rintro (rfl | rfl)
    · exact ⟨Or.inr le_rfl, le_rfl⟩
    · exact ⟨Or.inl rfl, hb.le⟩

/-- 概要：末尾一点追加後に錐頂点より大きい点は追加した点だけ。
方針：先頭集合の点は錐頂点以下なので残らない。
規約：HA Proposition 1.3.1.10。使われ方：Bianchi における錐頂点の符号が負となる計算。 -/
lemma cospanPrefix_insert_above {n : ℕ} (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).filter (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < ·) = {b} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le]
  constructor
  · rintro ⟨rfl | hi, hgt⟩
    · rfl
    · exact False.elim (not_le_of_gt hgt hi)
  · rintro rfl
    exact ⟨Or.inl rfl, hb⟩

/-- 概要：末尾一点追加後の錐頂点における HA 符号は負一。
方針：錐頂点より大きい点の集合が一点であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚の残差恒等式の符号。 -/
lemma cospanPrefix_insert_sign {n : ℕ} (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) = -1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, cospanPrefix_insert_above b hb, Finset.card_singleton,
    Nat.cast_one, Int.negOnePow_one]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
