module
public import SerrePositivity.EInfinity.ComplexLimits.ConePrependIndex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeComponents

/-!
概要：始点付き単射による cone の対象と、通常部分の尾の添字を元の制限列へ戻す。
方針：零と後続元で元の定義を直接評価する。
規約：同じ元の対象を保持する。使われ方：全単射 pullback 成分の端点照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_obj_prepend {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) (i : Fin (m + 2)) :
    (normalizedTensorConeData A X Y c).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i) =
      (normalizedTensorConeData A X Y
        ((SimplexCategory.toCat.map
          (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c)).obj i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma coneTailOrderHom_prepend_of_ne_zero {n m : ℕ}
    (e : Fin (m + 1) ↪o Fin (n + 1)) (i : Fin (m + 2)) (hi : i ≠ 0) :
    coneTailOrderHom n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom i) = e (coneTailOrderHom m i) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom_succ, coneTailOrderHom_succ, coneTailOrderHom_succ]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
