module

public import SerrePositivity.InfinityCategories.F1.SquareOpposite

/-!
概要：四角形の反転は cospan を反転した span に移す。
方針：標準ホーンの二辺で比較し、標準単体の反転を計算する。
規約：正方形内部の選択に依存しない。使われ方：外周極限錐の厳密延長の基底照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma pushoutSpan_reverseGrid {X : SSet.{u}} (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) :
    pushoutSpan (reverseGrid F) =
      (hornReverseIso 2 2).hom ≫ SSet.opFunctor.map (pullbackCospan F) := by
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc, stableHornReverse_two_left, Category.assoc,
      ← CategoryTheory.Functor.map_comp]
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_bottomEdge,
      pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge]
    change squareBottomEdge ≫ reverseGrid F =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map (squareTopEdge ≫ F)
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  · rw [← Category.assoc, stableHornReverse_two_right, Category.assoc,
      ← CategoryTheory.Functor.map_comp]
    rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge,
      pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge]
    change squareLeftEdge ≫ reverseGrid F =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map (squareRightEdge ≫ F)
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    rfl

lemma pushoutSpan_reverseGrid_eq_of_cospan_eq {X : SSet.{u}}
    {F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (h : pullbackCospan F = pullbackCospan G) :
    pushoutSpan (reverseGrid F) = pushoutSpan (reverseGrid G) := by
  rw [pushoutSpan_reverseGrid, pushoutSpan_reverseGrid, h]

end SerrePositivity.KST.LocalizingInvariants
