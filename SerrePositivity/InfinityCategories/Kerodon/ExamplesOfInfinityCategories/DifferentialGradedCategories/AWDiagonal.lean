module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAdjacent

/-!
# AW の切断点を削除する境界和の相殺

概要：切断点自身を左右のどちらから削除した項も、隣接切断の項と符号を反転して相殺する。
方針：空集合を零とする切れ目の合成を定義し、隣接切断の集合の一致と有限和の相殺を使う。
規約：成分族の微分の方程式は仮定せず、対角項の代数的な和だけを比較する。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW の標準方程式の保存。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D}

/-- 概要：重ならない二つの部分集合に評価した合成を、空集合では零にして定義する。
方針：前の射の標準次数を固定し、後の射の次数を目標次数から引いて取る。
規約：次数が集合の濃度と一致しない場合も全域評価により零となる。
使われ方：Kerodon 2.5.8（Tag 00S0） の切断点削除項の共通の値。 -/
def awGapTerm {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (L U : Finset (Fin (n + 1))) (k : ℤ) : GradedHom R x z k :=
  _root_.SerrePositivity.DifferentialGraded.compose R (g.componentOrZero L (k - (1 - (U.card : ℤ))))
    (f.componentOrZero U (1 - (U.card : ℤ))) (by omega)

/-- 概要：切れ目の合成は後の射の集合が空なら零である。
方針：全域評価の空集合の値と合成の零の法則を使う。
規約：目標次数は任意。
使われ方：Kerodon 2.5.8（Tag 00S0） の最小切断点の境界項の消滅。 -/
lemma awGapTerm_empty_left {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (U : Finset (Fin (n + 1))) (k : ℤ) : awGapTerm g f ∅ U k = 0 := by
  unfold awGapTerm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_empty]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _

/-- 概要：切れ目の合成は前の射の集合が空なら零である。
方針：全域評価の空集合の値と合成の零の法則を使う。
規約：目標次数は任意。
使われ方：Kerodon 2.5.8（Tag 00S0） の最大切断点の境界項の消滅。 -/
lemma awGapTerm_empty_right {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (L : Finset (Fin (n + 1))) (k : ℤ) : awGapTerm g f L ∅ k = 0 := by
  unfold awGapTerm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_empty]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero _ _

/-- 概要：切断点を接頭または接尾から削除する二つの符号付き和は相殺する。
方針：昇順の番号付けで、隣接切断の集合は等しく符号が逆であることを使う。
規約：成分族と目標次数は任意である。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW の境界の対角項の相殺。 -/
lemma awDiagonal_sum_eq_zero {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) :
    (∑ i : J, (-1 : ℤ) ^ (J.filter (· < i.val)).card •
      awGapTerm g f (J.filter (· < i.val)) (J.filter (i.val ≤ ·)) k) +
      (∑ i : J, (-1 : ℤ) ^ (J.filter (· < i.val)).card •
        awGapTerm g f (J.filter (· ≤ i.val)) (J.filter (i.val < ·)) k) = 0 := by
  by_cases hJ : J.Nonempty
  · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hJ.card_pos)
    let e : Fin (r + 1) ≃o J := J.orderIsoOfFin hr
    let G (i : J) := (-1 : ℤ) ^ (J.filter (· < i.val)).card •
      awGapTerm g f (J.filter (· < i.val)) (J.filter (i.val ≤ ·)) k
    let F (i : J) := (-1 : ℤ) ^ (J.filter (· < i.val)).card •
      awGapTerm g f (J.filter (· ≤ i.val)) (J.filter (i.val < ·)) k
    change (∑ i : J, G i) + ∑ i : J, F i = 0
    rw [← Fintype.sum_equiv e.toEquiv (G ∘ e) G (fun _ ↦ rfl),
      ← Fintype.sum_equiv e.toEquiv (F ∘ e) F (fun _ ↦ rfl)]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sum_adjacent_cancel
    · have he : J.filter (· < (e 0).val) = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_before_orderIso]
        rfl
      change (-1 : ℤ) ^ (J.filter (· < (e 0).val)).card •
        awGapTerm g f (J.filter (· < (e 0).val)) (J.filter ((e 0).val ≤ ·)) k = 0
      rw [he, awGapTerm_empty_left, smul_zero]
    · have he : J.filter ((e (Fin.last r)).val < ·) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have hb := e.monotone (Fin.le_last (e.symm ⟨a, (Finset.mem_filter.mp ha).1⟩))
        rw [e.apply_symm_apply] at hb
        exact not_lt_of_ge hb (Finset.mem_filter.mp ha).2
      change (-1 : ℤ) ^ (J.filter (· < (e (Fin.last r)).val)).card •
        awGapTerm g f (J.filter (· ≤ (e (Fin.last r)).val))
          (J.filter ((e (Fin.last r)).val < ·)) k = 0
      rw [he, awGapTerm_empty_right, smul_zero]
    · intro i
      change (-1 : ℤ) ^ (J.filter (· < (e i.succ).val)).card •
        awGapTerm g f (J.filter (· < (e i.succ).val)) (J.filter ((e i.succ).val ≤ ·)) k =
          -((-1 : ℤ) ^ (J.filter (· < (e i.castSucc).val)).card •
            awGapTerm g f (J.filter (· ≤ (e i.castSucc).val))
              (J.filter ((e i.castSucc).val < ·)) k)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_succ_eq_neg e i, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.before_succ_eq_left e i,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.after_castSucc_eq_right e i, neg_smul]
  · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simp

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
