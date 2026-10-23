module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientIntervalPathEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.KanTensorComplex

/-! 係数 path の移送は、同じ二作用上の厳密な引き戻し比較も同値にする。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R] (Q : Complex R)
  {T : SSet.{max u v}} [KanComplex T]
  (a : T ⟶ complexPinchedSpace.{u, v} Q ⊗ complexPinchedSpace.{u, v} Q)

def dgGluingCoefficientPathPullbackMap :=
  pullback.map (dgGluingComplexPathSpaceEndpointPair.{u, v} Q) a
    (F2.arrowEndpointPair (complexPinchedSpace.{u, v} Q)) a
    (dgGluingCoefficientIntervalPathComparison.{u, v} Q) (𝟙 T) (𝟙 _)
    (by rw [Category.comp_id, dgGluingCoefficientIntervalPathComparison_endpoints])
    (by simp only [Category.comp_id, Category.id_comp])

lemma dgGluingCoefficientPathPullbackMap_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingCoefficientPathPullbackMap Q a) := by
  let : KanComplex (complexPinchedSpace.{u, v} Q ⊗ complexPinchedSpace.{u, v} Q) :=
    F2.kanComplex_tensor _ _
  let : Fibration (dgGluingComplexPathSpaceEndpointPair.{u, v} Q) :=
    dgGluingComplexPathSpaceEndpointPair_fibration Q
  let : Fibration (F2.arrowEndpointPair (complexPinchedSpace.{u, v} Q)) :=
    dgGluingCoefficientIntervalEndpoints_fibration Q
  exact F2.strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _
    (by rw [Category.comp_id, dgGluingCoefficientIntervalPathComparison_endpoints])
    (by simp only [Category.comp_id, Category.id_comp])
    (dgGluingCoefficientIntervalPathComparison_equivalence Q)
    (isSimplicialHomotopyEquivalence_id _) (isSimplicialHomotopyEquivalence_id _)

end SerrePositivity.InfinityCategories
