module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.SmallSpaceDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SpaceDiagramImage
public import SerrePositivity.KST.Fibration.QuasicategoryUniverseReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EquivalenceDescent
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalizationSourceIso

/-! # 元の空間値図式を、同じ指定辺の反転を保って小さい全充満標的へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {X : SSet.{u}} (F : (SSet.uliftFunctor.{u + 1, u}).obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

instance smallSpaceDiagramTarget_quasicategory : Quasicategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramTarget F) :=
  smallSimplicialSet_quasicategory.{u, u + 1} _

/-- 小さい標的の包含は、元の全写像空間の意味で充満忠実。 -/
theorem smallSpaceDiagramInclusion_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImage F))).isQCatEquivalence
    |>.isFullyFaithful |>.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.spaceDiagramImageInclusion_isFullyFaithful F)

/-- 元の図式による反転は、同じ辺の宇宙降下と全充満包含の反映で小さい図式へ移る。 -/
theorem smallSpaceDiagram_inverts (W : Set (X _⦋1⦌))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (ULift.up '' W)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram F) W := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.invertsEdges_of_ulift_post (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram F) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion F)
    (smallSpaceDiagramInclusion_isFullyFaithful F) W
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagram_inclusion]
  exact hF

end SerrePositivity.KST.Fibration
