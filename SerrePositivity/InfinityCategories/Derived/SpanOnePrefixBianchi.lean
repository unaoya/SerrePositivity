module
public import SerrePositivity.InfinityCategories.Derived.SpanIndexGeometry
public import SerrePositivity.InfinityCategories.DGNerve.ProperEquationBianchi

/-! # 固定一点を加えた後続集合の Bianchi

概要：固定一点を可変頂点集合に加えた方程式の右辺の微分には、余錐頂点の寄与だけが残る。
方針：他の内部点では削除と両切断が既知なので、その残差を全て消す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の脚側の残差整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：固定一点追加後の右辺の微分は余錐頂点の残差寄与に等しい。
方針：Bianchi の有限和から余錐頂点を分離し、それ以外の内部点の既知残差を消す。
規約：始点は先頭二点のいずれか。使われ方：脚側の未知方程式の整合条件。 -/
lemma differential_rhs_span_onePrefix_single {n : ℕ} (s : SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ spanSuffixFaces n ⊆ I → s.Equation I)
    (a : Fin (n + 4)) (ha : a < spanApex n) (k : ℤ)
    (hI : 2 ≤ (insert a (spanSuffixFaces n)).card)
    (hmin : a = (insert a (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hmax : Fin.last (n + 3) = (insert a (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert a (spanSuffixFaces n)).card : ℤ)) :
    differential A (s.rhs (insert a (spanSuffixFaces n)) a (Fin.last (n + 3)) k hI hmin hmax hk) =
      s.residualContribution (insert a (spanSuffixFaces n)) a (Fin.last (n + 3)) k hI hmin hmax hk
        (spanApex n)
        (Finset.mem_insert_of_mem ((mem_spanSuffixFaces_iff_le _).mpr le_rfl))
        ha (spanApex_lt_last n) := by
  let I := insert a (spanSuffixFaces n)
  have hA : spanApex n ∈ I :=
    Finset.mem_insert_of_mem ((mem_spanSuffixFaces_iff_le _).mpr le_rfl)
  rw [s.bianchi]
  rw [Finset.sum_eq_single (⟨spanApex n, hA⟩ : I)]
  · simp only [dite_eq_left (show a < spanApex n ∧ spanApex n < Fin.last (n + 3) from
      ⟨ha, spanApex_lt_last n⟩)]
  · intro j _ hjA
    by_cases hint : a < j.val ∧ j.val < Fin.last (n + 3)
    · rw [dite_eq_left hint]
      have hjne : j.val ≠ spanApex n := fun h => hjA (Subtype.ext h)
      have hjV : j.val ∈ spanSuffixFaces n := by
        rcases Finset.mem_insert.mp j.property with hja | hjV
        · exact False.elim ((ne_of_gt hint.1) hja)
        · exact hjV
      have hjgt : spanApex n < j.val :=
        lt_of_le_of_ne ((mem_spanSuffixFaces_iff_le j.val).mp hjV) hjne.symm
      rw [s.residualContribution_of_cuts I a (Fin.last (n + 3)) k hI hmin hmax hk
        j.val j.property hint.1 hint.2
        (hknown _ (span_leftCut_known I j.val hint.2))
        (hknown _ (span_rightCut_known I j.val hjgt)),
        s.residual_zero_of_equation _ (hknown _ (span_erase_known I j.val hjV)), smul_zero]
    · simp only [dite_eq_right hint]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
