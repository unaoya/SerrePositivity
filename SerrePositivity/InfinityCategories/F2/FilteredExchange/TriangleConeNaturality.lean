module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConeTetrahedronParameter

/-!
概要：元の実三角形の右錐は、全係数の写像に厳密に自然。
方針：元の右 prism の自然性を三角形の同じ座標制限へ移す。
規約：元の全図式を保持。使われ方：013 面の後合成係数の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の三角形の同じ右錐は、全係数の任意の写像に厳密に自然。 -/
lemma triangleRightConeParameter_naturality {P Q : SSet.{u}} (q : Q ⟶ P) :
    triangleRightConeParameter Q ≫ joinMap (Δ[1] ◁ q) (𝟙 Δ[0]) =
      (Δ[2] ◁ q) ≫ triangleRightConeParameter P := by
  have hs : (squareTriangle 0 ▷ Q) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] Q).hom ≫
      (Δ[1] ◁ (Δ[1] ◁ q)) =
    (Δ[2] ◁ q) ≫ (squareTriangle 0 ▷ P) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] P).hom := by
    apply SSet.hom_ext
    intro d
    rfl
  calc
    _ = ((squareTriangle 0 ▷ Q) ≫ (α_ (Δ[1] : SSet.{u}) Δ[1] Q).hom ≫
        (Δ[1] ◁ (Δ[1] ◁ q))) ≫ rightMappingSpacePrism (Δ[1] ⊗ P) := by
      simp only [triangleRightConeParameter, Category.assoc]
      rw [rightMappingSpacePrism_naturality]
    _ = _ := by
      rw [hs]
      simp only [triangleRightConeParameter, Category.assoc]

end SerrePositivity.InfinityCategories.F2
