module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ModuleDerivedFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniversePinchedIntervalFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedUniverseNaturality

/-! 元の複体パラメーターと実導来 Hom 作用を、共通宇宙の同じ区間族へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

def dgGluingUniverseModuleDerivedFamilyInterval {A : Complex R} {P Q : RightModule R C}
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (RightModule R C) P Q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v} A).hom ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
      (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftPinchedHomIso
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))).app
          (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C))).app
          (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q))).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _

lemma dgGluingUniverseModuleDerivedFamilyInterval_evaluate {A : Complex R}
    {P Q : RightModule R C}
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (RightModule R C) P Q) :
    ((Δ[1] : SSet.{max (u + 1) v w}) ◁
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v} A).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval R C f)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedFamilyInterval, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftPinchedIntervalFamily,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
