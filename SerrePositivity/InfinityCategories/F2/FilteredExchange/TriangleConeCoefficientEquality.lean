module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConeTetrahedronParameter
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RightConeCoefficient
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.StandardTriangleCone

/-!
概要：元の右 join prism の実三角形は、同じ全係数付き標準三角形錐と一致する。
方針：同じ実 prism と全係数の追加の両立を、標準二単体で計算する。
規約：元の全図式の厳密等式。使われ方：実四面体の残る三面の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実三角形の全係数付き右錐は、同じ標準三角形錐そのもの。 -/
lemma triangleRightConeParameter_eq_simplexCone (P : SSet.{u}) :
    triangleRightConeParameter P = simplexConeParameter 1 P := by
  have hp : (squareTriangle 0 ▷ P) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] P).hom ≫
      lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _)) =
    (β_ Δ[2] P).hom ≫ (P ◁ squareTriangle 0) := by
    apply SSet.hom_ext
    intro d
    rfl
  calc
    _ = ((β_ Δ[2] P).hom ≫ (P ◁ squareTriangle 0)) ≫
        (P ◁ rightMappingSpacePrism Δ[1]) ≫ rightConeCoefficient Δ[1] P := by
      rw [← hp]
      simp only [triangleRightConeParameter, rightMappingSpacePrism_coefficient, Category.assoc]
    _ = (β_ Δ[2] P).hom ≫ (P ◁ (joinStdSimplexIso 1 0).inv) ≫
        rightConeCoefficient Δ[1] P := by
      rw [Category.assoc, ← whiskerLeft_comp_assoc, squareTriangle_rightMappingSpacePrism]
    _ = _ := rfl

end SerrePositivity.InfinityCategories.F2
