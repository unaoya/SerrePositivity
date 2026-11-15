module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorTrianglePieces

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
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorTriangleData {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n where
  obj := strictRawModuleTensorTriangleObj A X P Q c τ
  hom I a b k hI ha hb hk := by
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    by_cases hbt : τ b = 2
    · by_cases haz : τ a = 0
      · exact cast (by rw [strictRawModuleTensorTrianglePinched_obj_zero A X P Q c τ a haz,
          strictRawModuleTensorTrianglePinched_obj_two A X P Q c τ b hbt])
          ((strictRawModuleTensorTrianglePinched A X P Q c τ).hom I a b k hI ha hb hk)
      · have hbz : τ b ≠ 0 := by rw [hbt]; decide
        exact cast (by rw [strictRawModuleTensorTriangleBack_obj A X P Q c τ a haz,
          strictRawModuleTensorTriangleBack_obj A X P Q c τ b hbz])
          ((strictRawModuleTensorTriangleBack A X P Q c τ).hom I a b k hI ha hb hk)
    · have hat : τ a ≠ 2 := by
        intro hat
        apply hbt
        exact le_antisymm (Fin.le_last _) (hat ▸ τ.monotone hab)
      exact cast (by rw [strictRawModuleTensorTriangleFront_obj A X P Q c τ a hat,
        strictRawModuleTensorTriangleFront_obj A X P Q c τ b hbt])
        ((strictRawModuleTensorTriangleFront A X P Q c τ).hom I a b k hI ha hb hk)

end SerrePositivity.EInfinity.BarrattEccles
