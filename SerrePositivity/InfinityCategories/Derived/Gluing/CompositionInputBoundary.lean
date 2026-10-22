module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TriangleBoundaryFamily
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift

/-! 同じ終辺を固定し、第一辺と対角辺の全入力から三角形境界を構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ intervalMappingSpace x y) (b : T ⟶ intervalMappingSpace x z)

lemma dgGluingCompositionInputBoundary_source :
    (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ intervalMappingUncurry b =
      (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ (horn₂₁.ι₀₁ ▷ T) ≫
        uncurry (a ≫ composableHomHornMap x g) := by
  rw [composableHomHornMap_first, intervalMappingUncurry_face_source,
    intervalMappingUncurry_face_source]

lemma dgGluingCompositionInputBoundary_target :
    (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ intervalMappingUncurry b =
      (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ (horn₂₁.ι₁₂ ▷ T) ≫
        uncurry (a ≫ composableHomHornMap x g) := by
  rw [composableHomHornMap_last, intervalMappingUncurry_face_target, edgeFamily_target]

def dgGluingCompositionInputBoundaryFamily : (boundary 2 : SSet.{u}) ⊗ T ⟶ X :=
  dgGluingTriangleBoundaryFamily (uncurry (a ≫ composableHomHornMap x g))
    (intervalMappingUncurry b) (dgGluingCompositionInputBoundary_source x g a b)
    (dgGluingCompositionInputBoundary_target x g a b)

lemma dgGluingCompositionInputBoundaryFamily_horn :
    (Subcomplex.homOfLE triangleBoundary_bicartSq.le₂₄ ▷ T) ≫
      dgGluingCompositionInputBoundaryFamily x g a b =
      uncurry (a ≫ composableHomHornMap x g) :=
  dgGluingTriangleBoundaryFamily_horn _ _ _ _

lemma dgGluingCompositionInputBoundaryFamily_first :
    (boundary.ι (2 : Fin 3) ▷ T) ≫ dgGluingCompositionInputBoundaryFamily x g a b =
      intervalMappingUncurry a := by
  rw [dgGluingCompositionInputBoundaryFamily, dgGluingTriangleBoundaryFamily_face_two,
    composableHomHornMap_first]

lemma dgGluingCompositionInputBoundaryFamily_diagonal :
    (boundary.ι (1 : Fin 3) ▷ T) ≫ dgGluingCompositionInputBoundaryFamily x g a b =
      intervalMappingUncurry b :=
  dgGluingTriangleBoundaryFamily_face_one _ _ _ _

lemma dgGluingCompositionInputBoundaryFamily_last :
    (boundary.ι (0 : Fin 3) ▷ T) ≫ dgGluingCompositionInputBoundaryFamily x g a b =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge := by
  rw [dgGluingCompositionInputBoundaryFamily, dgGluingTriangleBoundaryFamily_face_zero,
    composableHomHornMap_last]

end SerrePositivity.InfinityCategories
