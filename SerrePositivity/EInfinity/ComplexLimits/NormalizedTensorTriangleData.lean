module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePieces

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorTriangleData {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) n where
  obj := normalizedTensorTriangleObj A X Y c τ
  hom I a b k hI ha hb hk := by
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    by_cases hbt : τ b = 2
    · by_cases haz : τ a = 0
      · exact cast (by rw [normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz,
          normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt])
          ((normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk)
      · have hbz : τ b ≠ 0 := by rw [hbt]; decide
        exact cast (by rw [normalizedTensorTriangleBack_obj A X Y c τ a haz,
          normalizedTensorTriangleBack_obj A X Y c τ b hbz])
          ((normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk)
    · have hat : τ a ≠ 2 := by
        intro hat
        apply hbt
        exact le_antisymm (Fin.le_last _) (hat ▸ τ.monotone hab)
      exact cast (by rw [normalizedTensorTriangleFront_obj A X Y c τ a hat,
        normalizedTensorTriangleFront_obj A X Y c τ b hbt])
        ((normalizedTensorTriangleFront A X Y c τ).hom I a b k hI ha hb hk)

end SerrePositivity.EInfinity.ComplexLimits
