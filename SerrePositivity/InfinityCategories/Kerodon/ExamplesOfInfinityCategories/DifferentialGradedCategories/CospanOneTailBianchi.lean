module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanOneTailIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ProperEquationBianchi

/-! # 末尾一点を加えた集合の Bianchi の唯一の寄与

概要：先頭一点を欠く全ての集合の方程式が成り立つと、脚の右辺の微分には錐頂点の寄与だけが残る。
方針：それ以外の内部点では削除と両切断が既知なので、残差を全て消す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の δr_B・δr_C・δr_D の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：末尾一点を加えた集合の右辺の微分は錐頂点の残差寄与に等しい。
方針：主残差恒等式の有限和から錐頂点を分離し、他の内部点の既知残差を零にする。
規約：HA Proposition 1.3.1.10。使われ方：未知の脚の方程式の整合条件の抽出。 -/
lemma differential_rhs_cospan_oneTail_single {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3))
    (hknown : ∀ I, ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I → s.Equation I)
    (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) (k : ℤ)
    (hI : 2 ≤ (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).card)
    (ha : (0 : Fin (n + 4)) = (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hmax : b = (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)).card : ℤ)) :
    differential A (s.rhs (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 b k hI ha hmax hk) =
      s.residualContribution (insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 b k hI ha hmax hk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)
        (Finset.mem_insert_of_mem ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le _).mpr le_rfl))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n) hb := by
  let I := insert b (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n ∈ I :=
    Finset.mem_insert_of_mem ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le _).mpr le_rfl)
  rw [s.bianchi]
  rw [Finset.sum_eq_single (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n, hA⟩ : I)]
  · simp only [dite_eq_left (show 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b from
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_pos n, hb⟩)]
  · intro j _ hjA
    by_cases hint : (0 : Fin (n + 4)) < j.val ∧ j.val < b
    · rw [dite_eq_left hint]
      have hjne : j.val ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n := fun h => hjA (Subtype.ext h)
      have hjV : j.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
        rcases Finset.mem_insert.mp j.property with hjb | hjV
        · exact False.elim ((ne_of_lt hint.2) hjb)
        · exact hjV
      have hjlt : j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n :=
        lt_of_le_of_ne ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces_iff_le j.val).mp hjV) hjne
      rw [s.residualContribution_of_cuts I 0 b k hI ha hmax hk j.val j.property hint.1 hint.2
        (hknown _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_leftCut_known I j.val hjlt))
        (hknown _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_rightCut_known I j.val hint.1)),
        s.residual_zero_of_equation _ (hknown _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospan_erase_known I j.val hjV)), smul_zero]
    · simp only [dite_eq_right hint]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (differential_rhs_cospan_oneTail_single)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
