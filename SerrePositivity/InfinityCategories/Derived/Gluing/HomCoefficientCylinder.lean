module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientIntervalPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainHomotopyEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCylinderNaturality

/-! 実 gluing Hom から係数 path への元の鎖写像を、元 Hom の円柱からの extension へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingCoefficientCylinderExtension (X Y : DGGluingObject R C D M) :=
  dgGluingCochainCylinderExtension
    (dgGluingComplexPathStart (M.value X.left Y.right))
    (dgGluingComplexPathEnd (M.value X.left Y.right))
    (-dgGluingComplexPathPrimitive (M.value X.left Y.right))
    (dgGluingComplexPathNegativePrimitive_boundary (M.value X.left Y.right))

def dgGluingHomCoefficientCylinderExtension (X Y : DGGluingObject R C D M) :=
  dgGluingCochainCylinderMap (dgGluingHomTwoEndpointPath R C D M X Y) ≫
    dgGluingCoefficientCylinderExtension R C D M X Y

def dgGluingHomCoefficientCylinderPrism (X Y : DGGluingObject R C D M) :=
  dgGluingComplexPinchedCylinderPrism.{u, max u v w} (dgGluingHomComplex R C D M X Y) ≫
    complexPinchedMap.{u, max u v w} (dgGluingHomCoefficientCylinderExtension R C D M X Y)

lemma dgGluingHomCoefficientIntervalPath_uncurry_cylinder (X Y : DGGluingObject R C D M) :
    uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y) =
      dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v w}
          (dgGluingHomTwoEndpointPath R C D M X Y) ≫
        complexPinchedMap.{u, max u v w} (dgGluingCoefficientCylinderExtension R C D M X Y) := by
  rw [dgGluingHomCoefficientIntervalPath, uncurry_natural_left,
    dgGluingCoefficientIntervalPathComparison_uncurry]
  change ((Δ[1] : SSet.{max u v w}) ◁
    complexPinchedMap.{u, max u v w} (dgGluingHomTwoEndpointPath R C D M X Y)) ≫
      ((β_ (Δ[1] : SSet.{max u v w})
        (complexPinchedSpace.{u, max u v w}
          (dgGluingComplexPath (M.value X.left Y.right)))).hom ≫
        (dgGluingComplexPinchedHomotopy_of_cochain.{u, max u v w} _ _ _ _).h) = _
  rw [dgGluingComplexPinchedHomotopy_of_cochain_prism]
  rfl

lemma dgGluingHomCoefficientCylinderMapPrism_extension (X Y : DGGluingObject R C D M) :
    dgGluingComplexPinchedCylinderMapPrism.{u, max u v w}
        (dgGluingHomTwoEndpointPath R C D M X Y) ≫
      complexPinchedMap.{u, max u v w} (dgGluingCoefficientCylinderExtension R C D M X Y) =
        dgGluingHomCoefficientCylinderPrism R C D M X Y := by
  rw [dgGluingComplexPinchedCylinderMapPrism, Category.assoc, ← complexPinchedMap_comp]
  rfl

end SerrePositivity.InfinityCategories
