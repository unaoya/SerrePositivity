module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoefficientIntervalPathEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanTensorComplex

/-! 係数 path の移送は、同じ二作用上の厳密な引き戻し比較も同値にする。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R] (Q : Complex R)
  {T : SSet.{max u v}} [KanComplex T]
  (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q)

def dgGluingCoefficientPathPullbackMap :=
  pullback.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair.{u, v} Q) a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q)) a
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison.{u, v} Q) (𝟙 T) (𝟙 _)
    (by rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_endpoints])
    (by simp only [Category.comp_id, Category.id_comp])

lemma dgGluingCoefficientPathPullbackMap_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingCoefficientPathPullbackMap Q a) := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanComplex_tensor _ _
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair.{u, v} Q) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathSpaceEndpointPair_fibration Q
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} Q)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalEndpoints_fibration Q
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _
    (by rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_endpoints])
    (by simp only [Category.comp_id, Category.id_comp])
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientIntervalPathComparison_equivalence Q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
