module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanComparisonAWBoundaryExpansion

/-!
# AW 微分の削除項の共通表示

概要：非対角の削除項を削除後の AW 項へ、対角の削除項を切れ目の合成へ同定する。
方針：全域評価を非空な集合では通常の成分に戻し、集合と次数の一致を使う。
規約：成分族の標準方程式の追加仮定は使わない。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の二重境界和の対応と相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：切断点より左の削除項は全体集合から削除した AW 項に等しい。
方針：空でない削除成分の全域評価を戻し、左側削除の成分の等式を使う。
規約：全体の標準境界符号を付けたまま比較する。
使われ方：Kerodon 2.5.8（Tag 00S0） の非対角項の第一の対応。 -/
lemma awBoundaryLeftTerm_of_lt {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (j : Fin (n + 1)) (hj : j ∈ J) (hji : j < i.val)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm g f J i j k hk = (-1 : ℤ) ^ (J.filter (· < j)).card •
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g f (J.erase j) ⟨i.val, Finset.mem_erase.mpr ⟨ne_of_gt hji, i.property⟩⟩
        (k + 1) (by have := Finset.card_erase_add_one hj; omega) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq g ((J.filter (· ≤ i.val)).erase j)
    (1 - ((J.filter (· ≤ i.val)).card : ℤ) + 1)
    ⟨i.val, Finset.mem_erase.mpr
      ⟨ne_of_gt hji, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩⟩
    (by
      have hc := Finset.card_erase_add_one
        (show j ∈ J.filter (· ≤ i.val) from Finset.mem_filter.mpr ⟨hj, hji.le⟩)
      omega), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm_erase_left g f J i j hj hji k hk]

/-- 概要：切断点より右の削除項は全体集合から削除した AW 項に等しい。
方針：空でない削除成分の全域評価を戻し、右側削除の成分の等式を使う。
規約：Leibniz 符号は全体の標準境界符号に吸収されている。
使われ方：Kerodon 2.5.8（Tag 00S0） の非対角項の第二の対応。 -/
lemma awBoundaryRightTerm_of_lt {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (j : Fin (n + 1)) (hj : j ∈ J) (hij : i.val < j)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm g f J i j k hk = (-1 : ℤ) ^ (J.filter (· < j)).card •
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm g f (J.erase j) ⟨i.val, Finset.mem_erase.mpr ⟨ne_of_lt hij, i.property⟩⟩
        (k + 1) (by have := Finset.card_erase_add_one hj; omega) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq f ((J.filter (i.val ≤ ·)).erase j)
    (1 - ((J.filter (i.val ≤ ·)).card : ℤ) + 1)
    ⟨i.val, Finset.mem_erase.mpr
      ⟨ne_of_lt hij, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩⟩
    (by
      have hc := Finset.card_erase_add_one
        (show j ∈ J.filter (i.val ≤ ·) from Finset.mem_filter.mpr ⟨hj, hij.le⟩)
      omega), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm_erase_right g f J i j hj hij k hk]

/-- 概要：切れ目の合成は任意に指定した整合する二つの次数で評価できる。
方針：次数の等式から同じ全域評価となることを示し、斉次合成の一致を使う。
規約：集合が空でも成立する。
使われ方：Kerodon 2.5.8（Tag 00S0） の対角削除項を同じ切れ目の成分へそろえる。 -/
lemma awGapTerm_eq_comp {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (L U : Finset (Fin (n + 1))) (p q k : ℤ) (hp : p = 1 - (U.card : ℤ))
    (hk : p + q = k) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awGapTerm g f L U k =
      _root_.SerrePositivity.DifferentialGraded.compose R (g.componentOrZero L q) (f.componentOrZero U p) hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awGapTerm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.compose_eq_of_heq
  · have he : k - (1 - (U.card : ℤ)) = q := by omega
    subst he
    rfl
  · subst hp
    rfl
  · exact hp.symm
  · omega

private lemma erase_left_self {α : Type*} [LinearOrder α] (J : Finset α) (i : α) :
    (J.filter (· ≤ i)).erase i = J.filter (· < i) := by
  classical
  ext a
  simp only [Finset.mem_erase, Finset.mem_filter]
  exact ⟨fun h ↦ ⟨h.2.1, lt_of_le_of_ne h.2.2 h.1⟩,
    fun h ↦ ⟨ne_of_lt h.2, h.1, h.2.le⟩⟩

private lemma erase_right_self {α : Type*} [LinearOrder α] (J : Finset α) (i : α) :
    (J.filter (i ≤ ·)).erase i = J.filter (i < ·) := by
  classical
  ext a
  simp only [Finset.mem_erase, Finset.mem_filter]
  exact ⟨fun h ↦ ⟨h.2.1, lt_of_le_of_ne h.2.2 h.1.symm⟩,
    fun h ↦ ⟨ne_of_gt h.2, h.1, h.2.le⟩⟩

/-- 概要：接頭部分から切断点自身を消す項は前の切れ目の合成である。
方針：切断点の削除を狭義の接頭部分と同定し、切れ目の合成の次数をそろえる。
規約：最小切断点でも空集合の値が零として成立する。
使われ方：HA 1.3.1.13 の対角境界和の第一の同定。 -/
lemma awBoundaryLeftTerm_diag {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm g f J i i.val k hk = (-1 : ℤ) ^ (J.filter (· < i.val)).card •
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awGapTerm g f (J.filter (· < i.val)) (J.filter (i.val ≤ ·)) (k + 1) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryLeftTerm
  rw [erase_left_self, awGapTerm_eq_comp g f _ _
    (1 - ((J.filter (i.val ≤ ·)).card : ℤ))
    (1 - ((J.filter (· ≤ i.val)).card : ℤ) + 1) (k + 1) rfl
    (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.degree_add i.property; omega),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq f _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.right_nonempty i.property) rfl]

/-- 概要：接尾部分から切断点自身を消す項は後の切れ目の合成である。
方針：切断点の削除を狭義の接尾部分と同定し、切れ目の合成の次数をそろえる。
規約：最大切断点でも空集合の値が零として成立する。
使われ方：HA 1.3.1.13 の対角境界和の第二の同定。 -/
lemma awBoundaryRightTerm_diag {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm g f J i i.val k hk = (-1 : ℤ) ^ (J.filter (· < i.val)).card •
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awGapTerm g f (J.filter (· ≤ i.val)) (J.filter (i.val < ·)) (k + 1) := by
  have hc : (J.filter (i.val < ·)).card + 1 = (J.filter (i.val ≤ ·)).card := by
    have h := Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨i.property, le_rfl⟩)
    rw [erase_right_self] at h
    exact h
  have hp : 1 - ((J.filter (i.val < ·)).card : ℤ) =
      1 - ((J.filter (i.val ≤ ·)).card : ℤ) + 1 := by omega
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBoundaryRightTerm
  rw [erase_right_self, awGapTerm_eq_comp g f _ _
    (1 - ((J.filter (i.val ≤ ·)).card : ℤ) + 1)
    (1 - ((J.filter (· ≤ i.val)).card : ℤ)) (k + 1) hp.symm
    (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.degree_add i.property; omega),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq g _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWIndex.left_nonempty i.property) rfl]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
