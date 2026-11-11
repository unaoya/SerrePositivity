module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ResidualExpansion

/-! # 削除と切断合成の添字の一致

概要：一点を削除してから切断した合成を、元の切断の一方の成分の削除として表す。
方針：削除点の左右で場合を分け、片側の集合は不変、他方の濃度は一減ることを使う。
規約：HA Proposition 1.3.1.10。使われ方：実際の混合項を共通の合成値へそろえる。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：切断点より左の点を削除すると、左成分の次数だけが一上がった合成になる。
方針：右切断は変わらず、左切断では所属点の削除で濃度が一減ることを使う。
規約：HA Proposition 1.3.1.10。使われ方：左側の混合項の合成値の一致。 -/
lemma cutCompose_erase_left {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (j l : Fin (n + 1)) (hj : j ∈ I) (hjl : j < l)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1) :
    s.cutCompose (I.erase j) a b (k + 1) l =
      compose A
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ)))
        (s.homOrZero ((I.filter (· ≤ l)).erase j) a l
          (2 - ((I.filter (· ≤ l)).card : ℤ) + 1)) (by omega) := by
  have hR : (I.erase j).filter (l ≤ ·) = I.filter (l ≤ ·) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt hjl
  have hjL : j ∈ I.filter (· ≤ l) := Finset.mem_filter.mpr ⟨hj, hjl.le⟩
  have hdeg : 2 - (((I.filter (· ≤ l)).erase j).card : ℤ) =
      2 - ((I.filter (· ≤ l)).card : ℤ) + 1 := by
    have := Finset.card_erase_add_one hjL
    omega
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  rw [hR, Finset.filter_erase, hdeg, dite_eq_left (by omega)]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cutCompose_erase_left)


/-- 概要：切断点より右の点を削除すると、右成分の次数だけが一上がった合成になる。
方針：左切断は変わらず、右切断では所属点の削除で濃度が一減ることを使う。
規約：HA Proposition 1.3.1.10。使われ方：右側の混合項の合成値の一致。 -/
lemma cutCompose_erase_right {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (j l : Fin (n + 1)) (hj : j ∈ I) (hlj : l < j)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1) :
    s.cutCompose (I.erase j) a b (k + 1) l =
      compose A
        (s.homOrZero ((I.filter (l ≤ ·)).erase j) l b
          (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1))
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))) (by omega) := by
  have hL : (I.erase j).filter (· ≤ l) = I.filter (· ≤ l) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt hlj
  have hjR : j ∈ I.filter (l ≤ ·) := Finset.mem_filter.mpr ⟨hj, hlj.le⟩
  have hdeg : 2 - (((I.filter (l ≤ ·)).erase j).card : ℤ) =
      2 - ((I.filter (l ≤ ·)).card : ℤ) + 1 := by
    have := Finset.card_erase_add_one hjR
    omega
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  rw [hL, Finset.filter_erase, hdeg, dite_eq_left (by omega)]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (cutCompose_erase_right)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
