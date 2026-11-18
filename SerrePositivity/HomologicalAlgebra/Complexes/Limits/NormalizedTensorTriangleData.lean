module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePieces

/-!
概要：元の三つの実単体の cochain を端点表示を保って貼り合わせる。
方針：元の引き戻し単体・実射・端点の等式輸送を保持する。
規約：全 HA 方程式は別工程。使われ方：大域評価三角形の実混合単体。
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

def normalizedTensorTriangleData {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) n where
  obj := _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A X Y c τ
  hom I a b k hI ha hb hk := by
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    by_cases hbt : τ b = 2
    · by_cases haz : τ a = 0
      · exact cast (by rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz,
          _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt])
          ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk)
      · have hbz : τ b ≠ 0 := by rw [hbt]; decide
        exact cast (by rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack_obj A X Y c τ a haz,
          _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack_obj A X Y c τ b hbz])
          ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
    · have hat : τ a ≠ 2 := by
        intro hat
        apply hbt
        exact le_antisymm (Fin.le_last _) (hat ▸ τ.monotone hab)
      exact cast (by rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_obj A X Y c τ a hat,
        _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_obj A X Y c τ b hbt])
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk)

end SerrePositivity.ComplexLimits
