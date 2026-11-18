module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMixedEquation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePinchedEquation

/-!
概要：元の全切断和・線形境界の比較から、実三相データの全 HA を証明する。
方針：元の零・中央・二相の全成分を比較し、同じ実単体の方程式を戻す。
規約：面・退化自然性と大域的な接合は別工程。使われ方：大域評価三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_equation {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).hom I a b k hI ha hb hk) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).rhs I a b k hI ha hb hk := by
  by_cases hbt : τ b = 2
  · by_cases haz : τ a = 0
    · by_cases hc : 3 ≤ I.card
      · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_equation_mixed A X Y c τ I hI hc a b k ha hb hk haz hbt
      · have hc2 : I.card = 2 := by omega
        have ham : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
        have hbm : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
        have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc2 ham hbm
        have h1 : ∀ i ∈ I, τ i ≠ 1 := by
          intro i hi
          rw [he] at hi
          rcases (show i = a ∨ i = b by simpa only [Finset.mem_insert, Finset.mem_singleton]
            using hi) with rfl | rfl
          · rw [haz]; decide
          · rw [hbt]; decide
        exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_equation_pinched A X Y c τ I h1 a b k hI ha hb hk
    · have h0 : ∀ i ∈ I, τ i ≠ 0 := by
        intro i hi hti
        apply haz
        have hai : a ≤ i := by rw [ha]; exact I.min'_le i hi
        exact le_antisymm (hti ▸ τ.monotone hai) (Fin.zero_le _)
      exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_equation_back A X Y c τ I h0 a b k hI ha hb hk
  · have h2 : ∀ i ∈ I, τ i ≠ 2 := by
      intro i hi hti
      apply hbt
      have hib : i ≤ b := by rw [hb]; exact I.le_max' i hi
      exact le_antisymm (Fin.le_last _) (hti ▸ τ.monotone hib)
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_equation_front A X Y c τ I h2 a b k hI ha hb hk

def normalizedTensorTriangleSimplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n where
  toSimplexData := _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ
  equation := _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_equation A X Y c τ

end SerrePositivity.ComplexLimits
