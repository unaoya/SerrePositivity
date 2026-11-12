module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreSourceComparisons
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：実 θ と元の始点の比較辺の合成を、同じ錐の圏で照合する。
方針：正規化した制限と全三辺を保持する実二単体を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第一合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open SimplicialObject.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma normalizedConeRestriction_cone {K L X : SSet.{u}} (p : K ⟶ X) (i : L ⟶ K)
    {q : L ⟶ X} (hi : i ≫ p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedConeRestriction p i hi).app (Opposite.op ⦋0⦌) c =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c i).cast hi := by
  cases hi
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
