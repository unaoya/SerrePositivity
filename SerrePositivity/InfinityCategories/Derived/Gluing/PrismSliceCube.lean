module
public import SerrePositivity.InfinityCategories.F1.SlicePrismSquare

/-! 同じ実 slice 合成 prism に沿う変換の三次元族を作り、三方向の境界を全パラメータで回収。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {X Y P : SSet.{u}} (V : (Δ[1] : SSet.{u}) ⊗ X ⟶ Y) (z : X _⦋0⦌)
  (W : (Δ[1] : SSet.{u}) ⊗ P ⟶ sliceOver (SSet.yonedaEquiv.symm z))

def dgGluingPrismSliceCube : Δ[1] ⊗ (Δ[1] ⊗ (Δ[1] ⊗ P)) ⟶ Y :=
  (Δ[1] ◁ slicePrismSquare z W) ≫ V

lemma dgGluingPrismSliceCube_outer (i : Fin 2) :
    prismEndpoint i _ ≫ dgGluingPrismSliceCube V z W =
      slicePrismSquare z W ≫ prismEndpoint i X ≫ V := by
  rw [dgGluingPrismSliceCube, ← Category.assoc, prismEndpoint_naturality, Category.assoc]

lemma dgGluingPrismSliceCube_middle_zero :
    (Δ[1] ◁ prismEndpoint 0 _) ≫ dgGluingPrismSliceCube V z W =
      (Δ[1] ◁ (W ≫ sliceOverProjection (SSet.yonedaEquiv.symm z))) ≫ V := by
  rw [dgGluingPrismSliceCube, ← Category.assoc, ← whiskerLeft_comp, slicePrismSquare_zero]

lemma dgGluingPrismSliceCube_middle_one :
    (Δ[1] ◁ prismEndpoint 1 _) ≫ dgGluingPrismSliceCube V z W =
      (Δ[1] ◁ SSet.const (X := Δ[1] ⊗ P) z) ≫ V := by
  rw [dgGluingPrismSliceCube, ← Category.assoc, ← whiskerLeft_comp, slicePrismSquare_one]

lemma dgGluingPrismSliceCube_inner (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i P)) ≫ dgGluingPrismSliceCube V z W =
      (Δ[1] ◁ (rightMappingSpacePrism P ≫
        sliceOverUncurry (prismEndpoint i P ≫ W))) ≫ V := by
  rw [dgGluingPrismSliceCube, ← Category.assoc, ← whiskerLeft_comp, slicePrismSquare_inner]

lemma dgGluingPrismSliceCube_outer_face {f : X ⟶ Y} (i : Fin 2)
    (hi : prismEndpoint i X ≫ V = f) :
    prismEndpoint i _ ≫ dgGluingPrismSliceCube V z W = slicePrismSquare z W ≫ f := by
  rw [dgGluingPrismSliceCube_outer, hi]

end SerrePositivity.InfinityCategories
