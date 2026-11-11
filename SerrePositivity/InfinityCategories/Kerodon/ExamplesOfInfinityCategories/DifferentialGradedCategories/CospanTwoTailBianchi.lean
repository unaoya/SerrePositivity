module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanTwoTailIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanOneTailBianchi

/-! # 末尾二点を加えた集合の Bianchi の二寄与

概要：標準セル全体の右辺の微分では錐頂点と最初の末尾頂点の寄与だけが残る。
方針：その他の内部点は先頭の真に小さい点なので、削除と両切断の既知残差が零になる。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：三角形成分の残差整合条件の抽出。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：標準セル全体の右辺の微分は錐頂点と最初の末尾頂点の残差寄与の和。
方針：主残差恒等式の有限和をその二点へ制限し、他の内部点の既知残差を消す。
規約：HA Proposition 1.3.1.10。使われ方：δr_BD・δr_CD の三項の整合条件。 -/
lemma differential_rhs_cospan_twoTail_pair {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A (s.rhs Finset.univ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) k hI ha hb hk) =
      s.residualContribution Finset.univ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) k hI ha hb hk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) (Finset.mem_univ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)) +
      s.residualContribution Finset.univ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) k hI ha hb hk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (Finset.mem_univ _)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n) := by
  let V : Finset (Fin (n + 4)) := Finset.univ
  let a : V := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n, Finset.mem_univ _⟩
  let b : V := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n, Finset.mem_univ _⟩
  let f : V → GradedHom A (s.obj 0) (s.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)) (k + 1 + 1) := fun j =>
    if h : 0 < j.val ∧ j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n then
      s.residualContribution V 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) k hI ha hb hk j.val j.property h.1 h.2
    else 0
  have hab : a ≠ b := by
    intro h
    exact (ne_of_lt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)) (congrArg Subtype.val h)
  rw [s.bianchi]
  change (∑ j : V, f j) = _
  have hsum : (∑ j : V, f j) = ∑ j ∈ ({a, b} : Finset V), f j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hjnot
    have hjA : j.val ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n := by
      intro h
      exact hjnot (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
    have hjB : j.val ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n := by
      intro h
      exact hjnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
    dsimp only [f]
    by_cases hint : (0 : Fin (n + 4)) < j.val ∧ j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n
    · rw [dite_eq_left hint]
      have hjV : j.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
        rcases _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanVertex_cases j.val with h | h | h
        · exact h
        · exact False.elim (hjB h)
        · exact False.elim ((ne_of_lt hint.2) h)
      have hjlt : j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n :=
        lt_of_le_of_ne ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le j.val).mp hjV) hjA
      rw [s.residualContribution_of_cuts V 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) k hI ha hb hk
        j.val j.property hint.1 hint.2
        (hknown _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_leftCut_known V j.val hjlt))
        (hknown _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_rightCut_known V j.val hint.1)),
        s.residual_zero_of_equation _ (hknown _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_erase_known V j.val hjV)), smul_zero]
    · simp only [dite_eq_right hint]
  rw [hsum, Finset.sum_pair hab]
  dsimp only [f, a, b]
  rw [dite_eq_left (show 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n from
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)⟩),
    dite_eq_left (show 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n from
      ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n⟩)]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (differential_rhs_cospan_twoTail_pair)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
