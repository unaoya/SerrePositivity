module

public import SerrePositivity.KST.Comparison.GammaH0
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ClosedComposition
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Γ の零次の環と閉零自己射

概要：AW 環の零次単体を閉次数零自己射の環に同定する。
方針：唯一の非空頂点集合での評価で、AW 積を通常の dg 合成と同定する。
規約：End の積 g*f は f≫g。SS03 (2.9) と同じ通常順を使う。
使われ方：π₀Γ と H⁰ の環比較の代表元での計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.Comparison

open CategoryTheory DifferentialGraded


variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/--
概要：零次単体の AW 積の閉元は閉元の通常順の dg 合成である。
方針：零次の切断点は一つなので AW の和が一項に縮む。
規約：SS03 (2.9) の積の次数零の計算。
使われ方：Γ の零次環から閉自己射の環への乗法性。
-/
theorem standardZeroEval_mul (x : D) (g f : GammaEnd (R := R) x 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval x x (g * f)).val =
      compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval x x g).val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval x x f).val (by decide) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g.val f.val).component Finset.univ 0 Finset.univ_nonempty (by simp) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, Finset.sum_eq_single
    (⟨0, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin 1)))]
  · unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
    have hl : (Finset.univ : Finset (Fin 1)).filter (· ≤ 0) = Finset.univ := by
      ext i; fin_cases i; simp
    have hr : (Finset.univ : Finset (Fin 1)).filter (0 ≤ ·) = Finset.univ := by
      ext i; fin_cases i; simp
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.compose_eq_of_heq
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq g.val _ Finset.univ hl _ 0
        (by simp) Finset.univ_nonempty rfl (by simp)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.component_heq_of_eq f.val _ Finset.univ hr _ 0
        (by simp) Finset.univ_nonempty rfl (by simp)
    · simp
    · simp
  · intro i _ hi
    exact (hi (Subsingleton.elim _ _)).elim
  · simp

/--
概要：Γ の零次単体の環を閉零自己射の環に同定する。
方針：閉元への線形同値と閉零射への同値を合成し、加法・乗法を確認する。
規約：SS03 (2.9)、既存の Koszul 符号と End の乗法規約を保つ。
使われ方：H⁰ の環比較を商へ降ろす際の代表写像。
-/
def gammaZeroClosedRingEquiv (x : D) : GammaEnd (R := R) x 0 ≃+*
    End (ForgetEnrichment.of (Complex R) x) where
  toEquiv := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) x x).toEquiv.trans
    (closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x)).symm).trans
      End.homEquiv.symm
  map_add' a b := by
    apply End.homEquiv.injective
    apply (closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x)).injective
    change (closedHomEquiv R D (ForgetEnrichment.of (Complex R) x)
      (ForgetEnrichment.of (Complex R) x))
        ((closedHomEquiv R D (ForgetEnrichment.of (Complex R) x)
          (ForgetEnrichment.of (Complex R) x)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv x x (a + b))) =
      (closedHomEquiv R D (ForgetEnrichment.of (Complex R) x)
        (ForgetEnrichment.of (Complex R) x))
          ((closedHomEquiv R D (ForgetEnrichment.of (Complex R) x)
            (ForgetEnrichment.of (Complex R) x)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv x x a) +
           (closedHomEquiv R D (ForgetEnrichment.of (Complex R) x)
            (ForgetEnrichment.of (Complex R) x)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv x x b))
    rw [closedHomEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact map_add (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) x x) a b
  map_mul' g f := by
    apply End.homEquiv.injective
    apply (closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x)).injective
    apply Subtype.ext
    change (closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x) ((closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv x x (g * f)))).val =
      (closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x) ((closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv x x f) ≫
        (closedHomEquiv R D
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) x)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv x x g))).val
    rw [Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact standardZeroEval_mul x g f

end SerrePositivity.KST.Comparison
