module

public import SerrePositivity.InfinityCategories.F2.NativeConeTriangle
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.InfinityCategories.Stable.CommutativeSquareRealization

/-!
概要：cospan 錐の正方形表示の下辺・左辺を、元の二つの錐の脚へ戻す。
方針：元の join 三角形の先頭の辺を制限する。
規約：二次の可換性も同じ錐のまま。使われ方：strict な BF pullback 錐の四辺の回収。
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
variable {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : JoinCone p)

lemma coneSquare_bottom_leg : squareBottomEdge ≫ coneSquare c =
    (joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) ≫ c.val := by
  have ht : squareTriangle 1 ≫ cospanConeSquareIso.inv = cospanConeTriangleLeft := by
    rw [← cospanConeSquareIso_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← stableSquareTriangle_bottomEdge, Category.assoc]
  change stdSimplex.δ (2 : Fin 3) ≫
    ((squareTriangle 1 ≫ cospanConeSquareIso.inv) ≫ c.val) = _
  rw [ht, ← Category.assoc]
  change (stdSimplex.δ ((1 : Fin 2).succ) ≫ F2.coneTriangleInclusion horn₂₂.ι₀₂) ≫ c.val = _
  rw [F2.coneTriangleInclusion_face, Category.assoc]

lemma coneSquare_left_leg : squareLeftEdge ≫ coneSquare c =
    (joinStdSimplexIso 0 0).inv ≫
      joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂) ≫ c.val := by
  have ht : squareTriangle 0 ≫ cospanConeSquareIso.inv = cospanConeTriangleRight := by
    rw [← cospanConeSquareIso_right, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← stableSquareTriangle_leftEdge, Category.assoc]
  change stdSimplex.δ (2 : Fin 3) ≫
    ((squareTriangle 0 ≫ cospanConeSquareIso.inv) ≫ c.val) = _
  rw [ht, ← Category.assoc]
  change (stdSimplex.δ ((1 : Fin 2).succ) ≫ F2.coneTriangleInclusion horn₂₂.ι₁₂) ≫ c.val = _
  rw [F2.coneTriangleInclusion_face, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants
