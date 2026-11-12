module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModuleDerivedClosedFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseSimplexConstantFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseModuleDerivedFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedCompatibility

/-! 共通宇宙での閉 augmentation の定値族は、元の実導来辺の同じ区間図式。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseModuleDerivedFamilyInterval_closed (A : Complex R)
    {P Q : RightModule R C}
    (s : ForgetEnrichment.of (Complex R) P ⟶ ForgetEnrichment.of (Complex R) Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
      (SSet.const (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) s))) =
    fst (Δ[1] : SSet.{max (u + 1) v w})
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} A)) ≫
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app
        (Opposite.op ⦋1⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R C) s).edge)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval_closed R C,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily_constant, whiskerLeft_fst_assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
