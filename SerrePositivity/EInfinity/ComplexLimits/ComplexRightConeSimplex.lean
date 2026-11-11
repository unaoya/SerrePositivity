module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeTerminalTerm
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeFrontEquation

/-!
概要：指定 augmentation を持つ実複体の任意 dg 単体に、同じ終端を追加した実単体を作る。
方針：前面は元の HA、終端を含む集合は閉性と各内部項の相殺で全方程式を証明する。
規約：存在を追加仮定しない。使われ方：元の cone の二重 cone と全三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexRightConeData_equation_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X) (I : Finset (Fin (n + 2)))
    (hl : Fin.last (n + 1) ∈ I) : (complexRightConeData A η).Equation I := by
  intro a b k hI ha hb hk
  have hbl : b = Fin.last (n + 1) := hb.trans
    ((I.isGreatest_max' _).unique ⟨hl, fun _ _ => Fin.le_last _⟩)
  rw [complexRightConeData_differential_last A η I a b k hI ha hb hk hbl]
  symm
  apply Finset.sum_eq_zero
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint]
    exact complexRightConeData_term_last A η I a b k hI ha hb hk hbl j.val j.property
      hint.1 hint.2
  · simp only [dite_eq_right hint]

def complexRightConeSimplex {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) where
  toSimplexData := complexRightConeData A η
  equation I := by
    by_cases hl : Fin.last (n + 1) ∈ I
    · exact complexRightConeData_equation_last A η I hl
    · exact complexRightConeData_equation_without_last A η I hl

lemma complexRightConeSimplex_data {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X) :
    (complexRightConeSimplex A η).toSimplexData = complexRightConeData A η := rfl

lemma complexRightConeSimplex_front {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X) :
    (complexRightConeSimplex A η).pullback Fin.castSuccOrderEmb.toOrderHom = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data]
  exact complexRightConeData_front A η

end SerrePositivity.EInfinity.ComplexLimits
