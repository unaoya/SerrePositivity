module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoefficientIntervalPathEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTwoEndpointProduct

/-! 元の gluing Hom の同じ path を、νf から gμ への係数空間内の実区間族にする。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomCoefficientIntervalPath (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTwoEndpointPath R C D M X Y) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison.{u, max u v w} (M.value X.left Y.right)

lemma dgGluingHomCoefficientIntervalPath_start (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingHomCoefficientIntervalPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) := by
  rw [dgGluingHomCoefficientIntervalPath, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_start, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTwoEndpointPath_start]

lemma dgGluingHomCoefficientIntervalPath_end (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingHomCoefficientIntervalPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) := by
  rw [dgGluingHomCoefficientIntervalPath, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_end, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTwoEndpointPath_end]

lemma dgGluingHomCoefficientIntervalPath_endpoints (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingHomCoefficientIntervalPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (M.value X.left Y.right)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTwoEndpointPath R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair.{u, max u v w} (M.value X.left Y.right) := by
  rw [dgGluingHomCoefficientIntervalPath, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_endpoints]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
