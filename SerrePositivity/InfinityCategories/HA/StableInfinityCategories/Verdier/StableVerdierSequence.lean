module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactFunctorCategoryEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
/-!
概要：安定 ∞ 圏の Verdier 列を全完全関手 ∞ 圏の普遍性で定義する。
方針：完全充満忠実な包含と完全な零化射に、全自然変換を含む商普遍性を課す。
規約：冪等完備化を追加しない。使われ方：Drinfeld 商の Verdier 列。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier
open CategoryTheory SSet
open scoped _root_.Simplicial
/-- 安定 ∞ 圏の包含と商が作る、全完全関手 ∞ 圏の意味での Verdier 列。 -/
structure IsStableVerdierSequence {B X Q : SSet.{u}}
    [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B] [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    [Quasicategory Q] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Q] (i : B ⟶ X) (q : X ⟶ Q) : Prop where
  fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i
  inclusionExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor i
  quotientExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q
  kills (z : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((i ≫ q).app (Opposite.op ⦋0⦌) z)
  universal (Y : SSet.{u}) [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] :
    let := quotientExact
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroingExactPrecomposition q (Set.range (i.app (Opposite.op ⦋0⦌)))
      (by rintro _ ⟨z, rfl⟩; exact kills z) Y)
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier
