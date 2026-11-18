module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleConstantOverlap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SimplexDataLocalEquation

/-!
概要：混合三角形の内部点が零相・二相なら、元の pinched 単体の全項を回収する。
方針：元の有限集合・全 cochain・切断の合成を端点の等式輸送と両立させる。
規約：中央相の切断和は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_term_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hbt : τ b = 2) (haz : τ a = 0) (hjz : τ j = 0) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).term I a b k hI ha hb hk j hj haj hjb)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).toSimplexData.term
        I a b k hI ha hb hk j hj haj hjb) := by
  have hx := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  have hjx := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_zero A X Y c τ j hjz).symm
  have hjt : τ j ≠ 2 := by rw [hjz]; decide
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.smul_sub_heq_of_obj_eq hx hy
  · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_pinched A X Y c τ _ _ _ _ _ _ _ _ hbt haz
  · refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq hx hjx hy rfl rfl rfl _ _ _ _ ?_ ?_ _ _
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_pinched A X Y c τ _ _ _ _ _ _ _ _ hbt hjz
    · refine (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ _ _ _ _ _ _ _ _ hjt).trans ?_
      apply _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_Pinched_zero_hom A X Y c τ
      intro i hi
      have hij : i ≤ j := (Finset.mem_filter.mp hi).2
      exact le_antisymm (hjz ▸ τ.monotone hij) (Fin.zero_le _)

lemma normalizedTensorTriangleData_term_two {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hbt : τ b = 2) (haz : τ a = 0) (hjt : τ j = 2) :
    HEq ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).term I a b k hI ha hb hk j hj haj hjb)
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).toSimplexData.term
        I a b k hI ha hb hk j hj haj hjb) := by
  have hx := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  have hjx := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_two A X Y c τ j hjt).symm
  have hjz : τ j ≠ 0 := by rw [hjt]; decide
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.smul_sub_heq_of_obj_eq hx hy
  · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_pinched A X Y c τ _ _ _ _ _ _ _ _ hbt haz
  · refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq hx hjx hy rfl rfl rfl _ _ _ _ ?_ ?_ _ _
    · refine (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_back A X Y c τ _ _ _ _ _ _ _ _ hbt hjz).trans ?_
      apply _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack_Pinched_two_hom A X Y c τ
      intro i hi
      have hji : j ≤ i := (Finset.mem_filter.mp hi).2
      exact le_antisymm (Fin.le_last _) (hjt ▸ τ.monotone hji)
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_pinched A X Y c τ _ _ _ _ _ _ _ _ hjt haz

end SerrePositivity.ComplexLimits
