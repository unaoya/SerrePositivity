module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FullyFaithfulIntervalMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingTrivial

/-!
概要：端点を正規化した元の区間 Hom の後合成に、同値性と全境界の持ち上げを移す。
方針：充満忠実な射の区間 Hom 作用を端点の等式で揃え、同値の右持ち上げを使う。
規約：元の intervalMappingPostOfEq そのものについて述べる。
使われ方：比較 path の Hom の両端評価の同値性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 充満忠実な射の、端点を正規化した同じ区間 Hom 作用は同値。 -/
lemma IsFullyFaithful.intervalMappingPostOfEq_isQCatEquivalence
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] {p : X ⟶ Y}
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌}
    (hx : p.app _ x = x') (hy : p.app _ y = y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y hx hy) := by
  subst x' y'
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalMappingPostOfEq_refl] using hp.intervalMappingPost_isQCatEquivalence x y

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsFullyFaithful (intervalMappingPostOfEq_isQCatEquivalence)


/-- 全境界を持ち上げる射の、同じ端点固定の区間 Hom 作用も全境界を持ち上げる。 -/
lemma intervalMappingPostOfEq_trivialKanFibration
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌}
    (hx : p.app _ x = x') (hy : p.app _ y = y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y hx hy) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p := by
    intro A B j hj _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) j hj
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration p).intervalMappingPostOfEq_isQCatEquivalence
    x y hx hy).trivialKanFibration_of_kanEquivalenceLifting
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanEquivalenceLifting_intervalMappingPostOfEq p hp x y hx hy)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
