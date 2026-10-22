module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridLeftPushout
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridFinalPushout
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridZeroValues

/-!
概要：外側の三面と中央面の共有辺・指定零頂点を厳密に照合する。
方針：値域を選ぶ前の nerve 内で全単体を比較し、同じ全図式で評価する。
規約：射の等式と元の零頂点を保持する。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionGridRightSquare_leftEdge :
    squareLeftEdge ≫ excisionGridRightSquare.{u} =
      squareRightEdge ≫ excisionGridCenterSquare ≫ nerveMap excisionGridCoreInclusion ≫
        nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  intro v
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

lemma excisionGridLeftSquare_leftEdge :
    squareLeftEdge ≫ excisionGridLeftSquare.{u} =
      squareTopEdge ≫ excisionGridCenterSquare ≫ nerveMap excisionGridCoreInclusion ≫
        nerveMap excisionGridMiddleInclusion := by
  apply thinNerveHom_ext_of_vertices
  intro v
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

lemma excisionGridFinalSquare_bottomEdge :
    squareBottomEdge ≫ excisionGridFinalSquare.{u} =
      squareTopEdge ≫ excisionGridRightSquare := by
  apply thinNerveHom_ext_of_vertices
  intro v
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

lemma excisionGridFinalSquare_leftEdge :
    squareLeftEdge ≫ excisionGridFinalSquare.{u} =
      squareTopEdge ≫ excisionGridLeftSquare := by
  apply thinNerveHom_ext_of_vertices
  intro v
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

lemma ExcisionGridExtension.right_square_zero {X : SSet.{u}}
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) : squareVertex (excisionGridRightSquare ≫ d.full) 1 0 = z :=
  d.first_new_zero

lemma ExcisionGridExtension.left_square_zero {X : SSet.{u}}
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) : squareVertex (excisionGridLeftSquare ≫ d.full) 1 0 = z :=
  d.second_new_zero
end SerrePositivity.InfinityCategories
