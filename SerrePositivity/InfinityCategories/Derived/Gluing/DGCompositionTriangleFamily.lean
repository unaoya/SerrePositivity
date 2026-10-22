module
public import SerrePositivity.InfinityCategories.Derived.Gluing.SlicePrismTriangleEndpoints
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyPrism

/-! native 合成 prism 自身から作る具体的な dg nerve 二単体族と、同じ指定三辺。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  {K : SSet.{max u v}} {x y z : D}
  (f : K ⟶ DGNerve.pinchedHom R D x y) (g : K ⟶ DGNerve.pinchedHom R D y z)

def dgGluingDGCompositionTriangleFamily : (Δ[2] : SSet.{max u v}) ⊗ K ⟶ dgNerve R D :=
  dgGluingSlicePrismTriangle (dgPinchedCompositionFamilyPrism R D f g)

lemma dgGluingDGCompositionTriangleFamily_two :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingDGCompositionTriangleFamily R D f g =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamily, dgGluingSlicePrismTriangle_front,
    dgPinchedCompositionFamilyPrism_projection]

lemma dgGluingDGCompositionTriangleFamily_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingDGCompositionTriangleFamily R D f g =
      intervalMappingUncurry (g ≫ pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamily, dgGluingSlicePrismTriangle_zero,
    dgPinchedCompositionFamilyPrism_one]
  simpa only [pinchedHomUncurry, dgPinchedHomSlice, Category.assoc] using
    (pinchedHomToIntervalMappingSpace_uncurry g).symm

lemma dgGluingDGCompositionTriangleFamily_one :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ dgGluingDGCompositionTriangleFamily R D f g =
      intervalMappingUncurry (pinchedHomCompositionFamily f g ≫
        pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamily, dgGluingSlicePrismTriangle_one,
    dgPinchedCompositionFamilyPrism_zero]
  simpa only [pinchedHomUncurry, dgPinchedHomSlice, Category.assoc] using
    (pinchedHomToIntervalMappingSpace_uncurry (pinchedHomCompositionFamily f g)).symm

end SerrePositivity.InfinityCategories
