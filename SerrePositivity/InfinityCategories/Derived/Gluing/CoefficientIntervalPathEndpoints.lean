module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientIntervalPathComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathProduct
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.ArrowEndpointPair

/-! 係数の実区間族への同じ同値は、元の端点対の上の厳密な比較である。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open HomotopicalAlgebra SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R] (Q : Complex R)

lemma dgGluingCoefficientIntervalPathComparison_endpoints :
    dgGluingCoefficientIntervalPathComparison.{u, v} Q ≫
        F2.arrowEndpointPair (complexPinchedSpace.{u, v} Q) =
      dgGluingComplexPathSpaceEndpointPair.{u, v} Q := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [F2.arrowEndpointPair, dgGluingComplexPathSpaceEndpointPair,
      Category.assoc, lift_fst]
    exact dgGluingCoefficientIntervalPathComparison_start Q
  · simp only [F2.arrowEndpointPair, dgGluingComplexPathSpaceEndpointPair,
      Category.assoc, lift_snd]
    exact dgGluingCoefficientIntervalPathComparison_end Q

lemma dgGluingCoefficientIntervalEndpoints_fibration :
    Fibration (F2.arrowEndpointPair (complexPinchedSpace.{u, v} Q)) := by
  rw [F2.arrowEndpointPair_restriction]
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  intro A B i hi
  let : HasLiftingProperty i
      ((pre F2.arrowBoundaryι).app (complexPinchedSpace.{u, v} Q)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance i hi
  infer_instance

end SerrePositivity.InfinityCategories
