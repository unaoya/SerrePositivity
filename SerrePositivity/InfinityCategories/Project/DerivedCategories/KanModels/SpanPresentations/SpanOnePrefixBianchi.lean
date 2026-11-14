module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanIndexGeometry
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ProperEquationBianchi

/-! # 固定一点を加えた後続集合の Bianchi

概要：固定一点を可変頂点集合に加えた方程式の右辺の微分には、余錐頂点の寄与だけが残る。
方針：他の内部点では削除と両切断が既知なので、その残差を全て消す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の脚側の残差整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：固定一点追加後の右辺の微分は余錐頂点の残差寄与に等しい。
方針：Bianchi の有限和から余錐頂点を分離し、それ以外の内部点の既知残差を消す。
規約：始点は先頭二点のいずれか。使われ方：脚側の未知方程式の整合条件。 -/
lemma differential_rhs_span_onePrefix_single {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I → s.Equation I)
    (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) (k : ℤ)
    (hI : 2 ≤ (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card)
    (hmin : a = (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hmax : Fin.last (n + 3) = (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card : ℤ)) :
    differential A (s.rhs (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) a (Fin.last (n + 3)) k hI hmin hmax hk) =
      s.residualContribution (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) a (Fin.last (n + 3)) k hI hmin hmax hk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
        (Finset.mem_insert_of_mem ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le _).mpr le_rfl))
        ha (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n) := by
  let I := insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)
  have hA : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n ∈ I :=
    Finset.mem_insert_of_mem ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le _).mpr le_rfl)
  rw [s.bianchi]
  rw [Finset.sum_eq_single (⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n, hA⟩ : I)]
  · simp only [dite_eq_left (show a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n ∧ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n < Fin.last (n + 3) from
      ⟨ha, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_lt_last n⟩)]
  · intro j _ hjA
    by_cases hint : a < j.val ∧ j.val < Fin.last (n + 3)
    · rw [dite_eq_left hint]
      have hjne : j.val ≠ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n := fun h => hjA (Subtype.ext h)
      have hjV : j.val ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
        rcases Finset.mem_insert.mp j.property with hja | hjV
        · exact False.elim ((ne_of_gt hint.1) hja)
        · exact hjV
      have hjgt : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n < j.val :=
        lt_of_le_of_ne ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le j.val).mp hjV) hjne.symm
      rw [s.residualContribution_of_cuts I a (Fin.last (n + 3)) k hI hmin hmax hk
        j.val j.property hint.1 hint.2
        (hknown _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_leftCut_known I j.val hint.2))
        (hknown _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_rightCut_known I j.val hjgt)),
        s.residual_zero_of_equation _ (hknown _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.span_erase_known I j.val hjV)), smul_zero]
    · simp only [dite_eq_right hint]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (differential_rhs_span_onePrefix_single)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
