module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CutErasure

/-! # 切断成分の境界の合成

概要：左右切断の成分に適用した境界を元の成分と合成し、その線形部分を削除後の切断で表す。
方針：左右の内部点集合を元の内部点集合の左右への制限で書き、合成を有限和へ分配する。
規約：HA Proposition 1.3.1.10。使われ方：実際の混合項の相殺への接続。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

namespace Index

/-- 概要：右切断の内部点は元の内部点のうち切断点より右にある点。
方針：左端と切断点の狭義不等式を使い、所属の三つの条件を同値変形する。
規約：HA Proposition 1.3.1.10。使われ方：右成分の境界の有限和の添字の移送。 -/
lemma interior_right_cut {α : Type*} [LinearOrder α] (I : Finset α) (a b j : α) (haj : a < j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior (I.filter (j ≤ ·)) j b = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·) := by
  ext x
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior, Finset.mem_filter]
  exact ⟨fun h => ⟨⟨h.1.1, haj.trans h.2.1, h.2.2⟩, h.2.1⟩,
    fun h => ⟨⟨h.1.1, h.2.le⟩, h.2, h.1.2.2⟩⟩

/-- 概要：左切断の内部点は元の内部点のうち切断点より左にある点。
方針：切断点と右端の狭義不等式を使い、所属の三つの条件を同値変形する。
規約：HA Proposition 1.3.1.10。使われ方：左成分の境界の有限和の添字の移送。 -/
lemma interior_left_cut {α : Type*} [LinearOrder α] (I : Finset α) (a b j : α) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior (I.filter (· ≤ j)) a j = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < j) := by
  ext x
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior, Finset.mem_filter]
  exact ⟨fun h => ⟨⟨h.1.1, h.2.1, h.2.2.trans hjb⟩, h.2.2⟩,
    fun h => ⟨⟨h.1.1, h.2.le⟩, h.1.2.1, h.2⟩⟩

end Index

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

namespace SimplexData

/-- 概要：一つ高い次数の射族を左右切断に評価し、元の反対側の成分と合成する。
方針：Leibniz 則と同じ二つの合成に右側成分の次数の符号を入れる。
規約：HA Proposition 1.3.1.10。使われ方：線形境界・合成境界・残差の合成部分の共通の形。 -/
def cutBoundary {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (B : ∀ (_I : Finset (Fin (n + 1))) a b k, GradedHom A (s.obj a) (s.obj b) (k + 1))
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1)) :
    GradedHom A (s.obj a) (s.obj b) (k + 1 + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    compose A (B (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)))
      (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))) (by omega) +
    (2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
      compose A (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)))
        (B (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))) (by omega)
  else 0

/-- 概要：切断成分の線形境界の合成は、左右の削除後の切断合成の二つの有限和に等しい。
方針：合成を有限和へ分配し、削除と切断の集合・次数の一致を各項で使う。
規約：HA Proposition 1.3.1.10。使われ方：実際の混合項を相殺の共通の値へそろえる。 -/
lemma cutBoundary_linear {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (l : Fin (n + 1)) (hl : l ∈ I) (hal : a < l) (hlb : l < b) :
    s.cutBoundary s.linearBoundary I a b k l =
      (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (l < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (l ≤ ·)) j •
        s.cutCompose (I.erase j) a b (k + 1) l) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
          s.cutCompose (I.erase j) a b (k + 1) l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hl
    omega
  unfold cutBoundary
  rw [dite_eq_left hsum]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.linearBoundary, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right,
    Index.interior_right_cut I a b l hal, Index.interior_left_cut I a b l hlb]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hmem := Finset.mem_filter.mp hj
    have hjI := (Finset.mem_filter.mp hmem.1).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose_erase_right s I a b k j l hjI hmem.2 hsum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hmem := Finset.mem_filter.mp hj
    have hjI := (Finset.mem_filter.mp hmem.1).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose_erase_left s I a b k j l hjI hmem.2 hsum]

end SimplexData

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
