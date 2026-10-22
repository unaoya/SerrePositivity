module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleFamily

/-! native の同じ具体的な合成三角形を実関手で後合成し、三つの全区間族を保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgGluingPinchedInterval_postcomp {K X Y : SSet.{u}} {x y : X _⦋0⦌}
    (f : K ⟶ InfinityCategories.pinchedHom x y) (q : X ⟶ Y) :
    intervalMappingUncurry ((f ≫ pinchedHomMap q x y) ≫ pinchedHomToIntervalMappingSpace _ _) =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace _ _) ≫ q := by
  rw [pinchedHomToIntervalMappingSpace_uncurry, pinchedHomUncurry_postcomp,
    pinchedHomToIntervalMappingSpace_uncurry, Category.assoc]

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  {K X : SSet.{max u v}} {x y z : D}
  (f : K ⟶ DGNerve.pinchedHom R D x y) (g : K ⟶ DGNerve.pinchedHom R D y z)
  (q : dgNerve R D ⟶ X)

def dgGluingDGCompositionTriangleFamilyPost : (Δ[2] : SSet.{max u v}) ⊗ K ⟶ X :=
  dgGluingDGCompositionTriangleFamily R D f g ≫ q

lemma dgGluingDGCompositionTriangleFamilyPost_two :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingDGCompositionTriangleFamilyPost R D f g q =
      intervalMappingUncurry ((f ≫ pinchedHomMap q (Simplex.vertex x) (Simplex.vertex y)) ≫
        pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamilyPost, ← Category.assoc,
    dgGluingDGCompositionTriangleFamily_two, ← dgGluingPinchedInterval_postcomp]

lemma dgGluingDGCompositionTriangleFamilyPost_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingDGCompositionTriangleFamilyPost R D f g q =
      intervalMappingUncurry ((g ≫ pinchedHomMap q (Simplex.vertex y) (Simplex.vertex z)) ≫
        pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamilyPost, ← Category.assoc,
    dgGluingDGCompositionTriangleFamily_zero, ← dgGluingPinchedInterval_postcomp]

lemma dgGluingDGCompositionTriangleFamilyPost_one :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ dgGluingDGCompositionTriangleFamilyPost R D f g q =
      intervalMappingUncurry ((pinchedHomCompositionFamily f g ≫
        pinchedHomMap q (Simplex.vertex x) (Simplex.vertex z)) ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingDGCompositionTriangleFamilyPost, ← Category.assoc,
    dgGluingDGCompositionTriangleFamily_one, ← dgGluingPinchedInterval_postcomp]

end SerrePositivity.InfinityCategories
