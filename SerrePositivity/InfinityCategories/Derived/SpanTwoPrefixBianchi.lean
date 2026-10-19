module
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixIndex
public import SerrePositivity.InfinityCategories.Derived.SpanOnePrefixBianchi

/-! # 固定二点を加えた集合の Bianchi の二寄与

概要：標準セル全体の右辺の微分では余錐頂点と二番目の固定頂点の寄与だけが残る。
方針：その他の内部点は余余錐頂点より後の点なので、削除と両切断の既知残差が零になる。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：三角形成分の残差整合条件の抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：標準セル全体の右辺の微分は余錐頂点と二番目の固定頂点の残差寄与の和。
方針：主残差恒等式の有限和をその二点へ制限し、他の内部点の既知残差を消す。
規約：HA Proposition 1.3.1.10。使われ方：三角形側右辺の微分の三項の整合条件。 -/
lemma differential_rhs_span_twoPrefix_pair {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ spanSuffixFaces n ⊆ I → s.Equation I) (k : ℤ)
    (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 4))).card)
    (ha : (0 : Fin (n + 4)) = Finset.univ.min' (Index.nonempty hI))
    (hb : Fin.last (n + 3) = Finset.univ.max' (Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 4))).card : ℤ)) :
    differential A (s.rhs Finset.univ 0 (Fin.last (n + 3)) k hI ha hb hk) =
      s.residualContribution Finset.univ 0 (Fin.last (n + 3)) k hI ha hb hk
        (spanApex n) (Finset.mem_univ _) (spanApex_pos n)
        (spanApex_lt_last n) +
      s.residualContribution Finset.univ 0 (Fin.last (n + 3)) k hI ha hb hk
        (spanSecondPrefix n) (Finset.mem_univ _)
        (spanSecondPrefix_pos n) ((spanSecondPrefix_lt_apex n).trans (spanApex_lt_last n)) := by
  let V : Finset (Fin (n + 4)) := Finset.univ
  let a : V := ⟨spanApex n, Finset.mem_univ _⟩
  let b : V := ⟨spanSecondPrefix n, Finset.mem_univ _⟩
  let f : V → GradedHom A (s.obj 0) (s.obj (Fin.last (n + 3))) (k + 1 + 1) := fun j =>
    if h : 0 < j.val ∧ j.val < Fin.last (n + 3) then
      s.residualContribution V 0 (Fin.last (n + 3)) k hI ha hb hk j.val j.property h.1 h.2
    else 0
  have hab : a ≠ b := by
    intro h
    exact (ne_of_gt (spanSecondPrefix_lt_apex n)) (congrArg Subtype.val h)
  rw [s.bianchi]
  change (∑ j : V, f j) = _
  have hsum : (∑ j : V, f j) = ∑ j ∈ ({a, b} : Finset V), f j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hjnot
    have hjA : j.val ≠ spanApex n := by
      intro h
      exact hjnot (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
    have hjB : j.val ≠ spanSecondPrefix n := by
      intro h
      exact hjnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
    dsimp only [f]
    by_cases hint : (0 : Fin (n + 4)) < j.val ∧ j.val < Fin.last (n + 3)
    · rw [dite_eq_left hint]
      have hjV : j.val ∈ spanSuffixFaces n := by
        rcases spanVertex_cases j.val with h | h | h
        · exact h
        · exact False.elim ((ne_of_gt hint.1) h)
        · exact False.elim (hjB h)
      have hjgt : spanApex n < j.val :=
        lt_of_le_of_ne ((mem_spanSuffixFaces_iff_le j.val).mp hjV) hjA.symm
      rw [s.residualContribution_of_cuts V 0 (Fin.last (n + 3)) k hI ha hb hk
        j.val j.property hint.1 hint.2
        (hknown _ (span_leftCut_known V j.val hint.2))
        (hknown _ (span_rightCut_known V j.val hjgt)),
        s.residual_zero_of_equation _ (hknown _ (span_erase_known V j.val hjV)), smul_zero]
    · simp only [dite_eq_right hint]
  rw [hsum, Finset.sum_pair hab]
  dsimp only [f, a, b]
  rw [dite_eq_left (show 0 < spanApex n ∧ spanApex n < Fin.last (n + 3) from
    ⟨spanApex_pos n, spanApex_lt_last n⟩),
    dite_eq_left (show 0 < spanSecondPrefix n ∧ spanSecondPrefix n < Fin.last (n + 3) from
      ⟨spanSecondPrefix_pos n, (spanSecondPrefix_lt_apex n).trans (spanApex_lt_last n)⟩)]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
