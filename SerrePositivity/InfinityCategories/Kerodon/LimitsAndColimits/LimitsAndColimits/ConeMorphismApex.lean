module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeValueProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HoHomVertexTransportCongr

/-!
概要：元の錐圏の射の全関手での頂点評価は、元の頂点射影の作用そのもの。
方針：一般の端点移送の合成則と、全錐の頂点射影の厳密な等式を使う。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の余単位と錐の比較。
規約：錐圏の元の射と頂点を保持し、大きい本文を展開しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の錐圏の射を全関手へ写して頂点で評価しても、元の頂点射影で写した射と同じ。 -/
lemma coneHoMorphismValue_apex {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (β : (SSet.HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ⟶
      SSet.HomotopyCategory.mk d) :
    functorHomEvaluate (coneHoMorphismValue β)
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)) =
        (hoFunctor.map (sliceOverProjection p)).toFunctor.map β := by
  let x := SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)
  change hoHomMapWithVertexEqualities (evaluateFunctorAt x)
    (evaluateFunctorAt_functorVertex x c.val) (evaluateFunctorAt_functorVertex x d.val)
    (hoHomMapWithVertexEqualities (coneValueProjection p)
      (coneValueProjection_vertex p c) (coneValueProjection_vertex p d) β) = _
  rw [hoHomMapWithVertexEqualities_comp]
  have h := hoHomMapWithVertexEqualities_congr (coneValueProjection_apex p)
    ((congrArg ((evaluateFunctorAt x).app (Opposite.op ⦋0⦌)) (coneValueProjection_vertex p c)).trans
      (evaluateFunctorAt_functorVertex x c.val))
    ((congrArg ((evaluateFunctorAt x).app (Opposite.op ⦋0⦌)) (coneValueProjection_vertex p d)).trans
      (evaluateFunctorAt_functorVertex x d.val)) rfl rfl β
  simpa only [hoHomMapWithVertexEqualities_refl] using h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
