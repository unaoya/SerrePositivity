module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTrianglePost
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorTriangleOfFamily
public import SerrePositivity.InfinityCategories.F1B.IntervalFamilySquare

/-! native の具体的な三角形族を、そのまま実導来関手の合成三角形として保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgGluingIntervalFamilyHomotopy_evaluate {K X : SSet.{u}} {x y : X _⦋0⦌}
    (f : K ⟶ intervalMappingSpace x y) :
    (β_ (Δ[1] : SSet.{u}) K).hom ≫ (intervalFamilyHomotopy f).h =
      intervalMappingUncurry f := by
  simp only [intervalFamilyHomotopy, ← Category.assoc, SymmetricCategory.symmetry,
    Category.id_comp]

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  {K X : SSet.{max u v}} {x y z : D}
  (f : K ⟶ DGNerve.pinchedHom R D x y) (g : K ⟶ DGNerve.pinchedHom R D y z)
  (q : dgNerve R D ⟶ X)

def dgGluingDGCompositionFunctorTriangle : FunctorCompositionTriangle
    (intervalFamilyHomotopy ((f ≫ pinchedHomMap q (Simplex.vertex x) (Simplex.vertex y)) ≫
      pinchedHomToIntervalMappingSpace _ _))
    (intervalFamilyHomotopy ((g ≫ pinchedHomMap q (Simplex.vertex y) (Simplex.vertex z)) ≫
      pinchedHomToIntervalMappingSpace _ _))
    (intervalFamilyHomotopy ((pinchedHomCompositionFamily f g ≫
      pinchedHomMap q (Simplex.vertex x) (Simplex.vertex z)) ≫
        pinchedHomToIntervalMappingSpace _ _)) :=
  dgGluingFunctorTriangleOfFamily _ _ _ (dgGluingDGCompositionTriangleFamilyPost R D f g q)
    ((dgGluingDGCompositionTriangleFamilyPost_zero R D f g q).trans
      (dgGluingIntervalFamilyHomotopy_evaluate _).symm)
    ((dgGluingDGCompositionTriangleFamilyPost_one R D f g q).trans
      (dgGluingIntervalFamilyHomotopy_evaluate _).symm)
    ((dgGluingDGCompositionTriangleFamilyPost_two R D f g q).trans
      (dgGluingIntervalFamilyHomotopy_evaluate _).symm)

end SerrePositivity.InfinityCategories
