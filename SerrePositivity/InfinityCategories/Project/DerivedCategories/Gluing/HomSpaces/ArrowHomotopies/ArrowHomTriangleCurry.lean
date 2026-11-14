module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.ArrowHomotopies.ArrowHomTrianglePair

/-! 同じ二つの合成三角形を貼り、元の矢印圏の全区間 Hom へ厳密に戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {T X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⟶ X}

def dgGluingArrowHomTriangleSquare (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ T ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.parameterizedSquareLift a.first a.second a.diagonal

lemma dgGluingArrowHomTriangleSquare_zero (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ▷ T) ≫ dgGluingArrowHomTriangleSquare a = fst Δ[1] T ≫ F := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_upper_left, comp_whiskerRight, Category.assoc,
    dgGluingArrowHomTriangleSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.parameterizedSquareLift_zero]
  exact a.source

lemma dgGluingArrowHomTriangleSquare_one (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] ▷ T) ≫ dgGluingArrowHomTriangleSquare a = fst Δ[1] T ≫ G := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_right, comp_whiskerRight, Category.assoc,
    dgGluingArrowHomTriangleSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.parameterizedSquareLift_one]
  exact a.target

def dgGluingArrowHomIntervalOfTriangles (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrismCurry (dgGluingArrowHomTriangleSquare a)
    (dgGluingArrowHomTriangleSquare_zero a) (dgGluingArrowHomTriangleSquare_one a)

lemma dgGluingArrowHomIntervalOfTriangles_prism
    (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (dgGluingArrowHomIntervalOfTriangles a) =
      dgGluingArrowHomTriangleSquare a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_curry _ _ _

lemma dgGluingArrowHomTriangles_interval (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval F G (dgGluingArrowHomIntervalOfTriangles a) = a := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair.ext
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism _ = _
    rw [dgGluingArrowHomIntervalOfTriangles_prism, dgGluingArrowHomTriangleSquare,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.parameterizedSquareLift_zero]
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism _ = _
    rw [dgGluingArrowHomIntervalOfTriangles_prism, dgGluingArrowHomTriangleSquare,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.parameterizedSquareLift_one]

def dgGluingArrowHomTriangleEquiv :
    (T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) ≃
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair (T := T) F G where
  toFun := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval F G
  invFun := dgGluingArrowHomIntervalOfTriangles
  left_inv f := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTrianglePairOfInterval_injective F G
    exact dgGluingArrowHomTriangles_interval _
  right_inv := dgGluingArrowHomTriangles_interval

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
