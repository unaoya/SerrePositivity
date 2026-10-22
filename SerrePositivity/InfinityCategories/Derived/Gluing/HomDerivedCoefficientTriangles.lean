module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedCoefficientTriangleDiagonals
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedHomCoefficientPathEndpoints

/-! 元の gluing Hom 上の二三角形の対角は、同じ実導来係数 path の両端である。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedLeftCoefficientTriangle (X Y : DGGluingObject R C D M) :=
  ((Δ[2] : SSet.{max (u + 1) v w}) ◁
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))) ≫
    dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y

def dgGluingHomDerivedRightCoefficientTriangle (X Y : DGGluingObject R C D M) :=
  ((Δ[2] : SSet.{max (u + 1) v w}) ◁
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) ≫
    dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y

lemma dgGluingHomDerivedLeftCoefficientTriangle_diagonal (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y =
      intervalMappingUncurry
        ((dgGluingDerivedHomCoefficientIntervalPath R C D M X Y ≫
            evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
            pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingHomDerivedLeftCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedLeftCoefficientTriangleFamily_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]
  apply congrArg intervalMappingUncurry
  rw [dgGluingDerivedHomCoefficientIntervalPath_start R C D M X Y]
  simp only [complexPinchedMap_comp, Functor.map_comp, Category.assoc]

lemma dgGluingHomDerivedRightCoefficientTriangle_diagonal (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingHomDerivedRightCoefficientTriangle R C D M X Y =
      intervalMappingUncurry
        ((dgGluingDerivedHomCoefficientIntervalPath R C D M X Y ≫
            evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
          (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
            pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingHomDerivedRightCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedRightCoefficientTriangleFamily_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]
  apply congrArg intervalMappingUncurry
  rw [dgGluingDerivedHomCoefficientIntervalPath_end R C D M X Y]
  simp only [complexPinchedMap_comp, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories
