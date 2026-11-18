module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SimplexDataNoninjectiveZero
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMiddleSums
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleSupport

/-!
概要：三相添字の非単射性により、元の二つの混合 cochain の消滅を示す。
方針：元の非単射添字・同相の二点・切断の一意性を使う。
規約：主場合の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
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

lemma normalizedTensorTriangleData_homOrZero_front_noninj {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (haz : τ a = 0) (hb1 : τ b = 1)
    (hi : ¬ Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ) (I : Set (Fin (n + 1)))) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).homOrZero I a b k = 0 := by
  have ha2 : τ a ≠ 2 := by rw [haz]; decide
  have hb2 : τ b ≠ 2 := by rw [hb1]; decide
  have hb0 : τ b ≠ 0 := by rw [hb1]; decide
  have hne : _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ a ≠ _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ b := by
    rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ a haz, _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ b hb0]
    exact (Fin.succ_ne_zero _).symm
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero
  split_ifs with hI ha hb hk
  · have hh := _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ I a b k hI ha hb hk hb2
    have hz := _root_.SerrePositivity.ComplexLimits.simplexData_pullback_hom_zero_of_not_inj_of_ne
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c).toSimplexData (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ)
      I a b k hI ha hb hk hi hne
    exact eq_of_heq (hh.trans ((heq_of_eq hz).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_obj A X Y c τ a ha2)
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_obj A X Y c τ b hb2) rfl)))
  all_goals rfl

lemma normalizedTensorTrianglePinched_homOrZero_back_noninj {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (ha1 : τ a = 1) (hbt : τ b = 2)
    (hi : ¬ Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) (I : Set (Fin (n + 1)))) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).toSimplexData.homOrZero I a b k = 0 := by
  have ha2 : τ a ≠ 2 := by rw [ha1]; decide
  have hne : _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ a ≠ _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ b := by
    rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ a ha2, _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ b hbt]
    exact Fin.castSucc_ne_last _
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero
  split_ifs with hI ha hb hk
  · exact _root_.SerrePositivity.ComplexLimits.simplexData_pullback_hom_zero_of_not_inj_of_ne
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.toSimplexData
      (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) I a b k hI ha hb hk hi hne
  all_goals rfl
end SerrePositivity.ComplexLimits
