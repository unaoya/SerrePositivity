module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConePrependIndex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeComponents

/-!
概要：始点付き単射による cone の対象と、通常部分の尾の添字を元の制限列へ戻す。
方針：零と後続元で元の定義を直接評価する。
規約：同じ元の対象を保持する。使われ方：全単射 pullback 成分の端点照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_obj_prepend {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (i : Fin (m + 2)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i) =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y
        ((SimplexCategory.toCat.map
          (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).obj i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma coneTailOrderHom_prepend_of_ne_zero {n m : ℕ}
    (e : Fin (m + 1) ↪o Fin (n + 1)) (i : Fin (m + 2)) (hi : i ≠ 0) :
    _root_.SerrePositivity.ComplexLimits.coneTailOrderHom n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i) = e (_root_.SerrePositivity.ComplexLimits.coneTailOrderHom m i) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom_succ, _root_.SerrePositivity.ComplexLimits.coneTailOrderHom_succ, _root_.SerrePositivity.ComplexLimits.coneTailOrderHom_succ]
  rfl

end SerrePositivity.ComplexLimits
