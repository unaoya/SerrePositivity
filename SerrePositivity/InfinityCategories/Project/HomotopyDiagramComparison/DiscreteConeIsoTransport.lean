module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.DiscreteConeArrowHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：元の離散全錐の指定頂点同値と全脚の可換式から、全錐の関手同型を構成する。
方針：同じ元の全脚正方形の円柱の全頂点での可逆性を使う。
規約：元の全錐と指定辺を保持する。底の充填性・有限性・比較族の自然性は仮定しない。
使われ方：標準有限積全錐から実際の前層余極限の全錐像への極限性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SSet.Truncated.HomotopyCategory
variable {J : Type u} {X : SSet.{u + 1}} [Quasicategory X]
  {p q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (e : SSet.Edge c.vertex d.vertex)
  (f : (j : J) → SSet.Edge
    (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))))
    (q.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))))
  (h : ∀ j, homMk e.toTruncated ≫
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))) =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))) ≫
      homMk (f j).toTruncated)

include h in
/-- 元の指定可逆辺と同じ全脚の可換式から、元の二つの全錐の関手同型を作る。 -/
def discreteConeIsoOfLegClasses
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated) (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (f j).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteConeArrowHomotopy c d e f h)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteConeArrowHomotopy_isInvertible c d e f h he hf)

include h in
/-- 指定した元の頂点同値と全脚の可換式に沿って、離散全錐の極限性を移す。 -/
lemma isLimitCone_iff_discreteLegClasses
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated) (hf : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (f j).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := by
  let i := discreteConeIsoOfLegClasses c d e f h he hf
  exact ⟨fun hc => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.of_functorIso hc i,
    fun hd => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.of_functorIso hd i.symm⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
