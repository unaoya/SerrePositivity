module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.ModuleDerivedFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.PinchedConstantIntervalFamilies

/-! 実閉加群射の導来区間族は、同じ閉辺の実導来像に定値な族。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingModuleDerivedFamilyInterval_closed {K : SSet.{max (u + 1) v}}
    {P Q : RightModule R C}
    (s : ForgetEnrichment.of (Complex R) P ⟶ ForgetEnrichment.of (Complex R) Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) s))) =
    fst (Δ[1] : SSet.{max (u + 1) v}) K ≫ SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))).app
        (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R C) s).edge) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedConstantIntervalFamily_post _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
