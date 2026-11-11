module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeClosed
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeFrontEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackEquation

/-!
概要：実右 cone の全二点集合は HA 方程式を満たす。
方針：終端が無ければ元の前面へ戻し、終端が有れば閉性と空の内部和を使う。
規約：指定 augmentation から実辺を構成する。使われ方：高次終端方程式への還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexRightConeData_equation_pair {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X) (I : Finset (Fin (n + 2))) (hc : I.card = 2) :
    (complexRightConeData A η).Equation I := by
  by_cases hl : Fin.last (n + 1) ∈ I
  · intro a b k hI ha hb hk
    have hbl : b = Fin.last (n + 1) := hb.trans
      ((I.isGreatest_max' _).unique ⟨hl, fun _ _ => Fin.le_last _⟩)
    rw [complexRightConeData_differential_last A η I a b k hI ha hb hk hbl,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_of_card_two _ I a b k hI ha hb hk hc]
  · exact complexRightConeData_equation_without_last A η I hl

end SerrePositivity.EInfinity.ComplexLimits
