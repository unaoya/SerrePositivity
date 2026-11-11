module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanQuotientValueEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceTriangleFaces

/-!
概要：元の実商比較と既存指定値比較の合成を、同じ Kan 値で零化する。
方針：同じ指定成分の逆関係を実三角形へ戻し、元の三辺の Kan 射を読む。
規約：両方の既存実辺を保持する。一般の transport・商 API は新設しない。
使われ方：K-B-S の全 fiber 単位を元の Kan 置換単位へ正規化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.obj)

/-- 概要：元の実比較辺と既存指定値比較辺の合成は、同じ Kan 値の恒等とホモトピック。
方針：指定値同型の両逆を実三角形へ読み戻し、その同じ三辺の Kan 射を評価する。
規約：辺を別の代表へ選び直さず、実三角形だけを選ぶ。
使われ方：全固定 fiber 回収の元の値座標での正規化。 -/
def weakSpanKanQuotientValueCancellationHomotopy :
    SSet.Homotopy
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj c))).obj)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientForwardValueEdgeAtValue h x c) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueEdge h x c)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientForwardValueEdgeAtValue h x c
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueEdge h x c
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj c)
  have hc : Truncated.HomotopyCategory.homMk e.toTruncated ≫
      Truncated.HomotopyCategory.homMk d.toTruncated =
      Truncated.HomotopyCategory.homMk (SSet.Edge.id z).toTruncated := by
    change Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientForwardValueEdgeAtValue h x c).toTruncated ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueEdge h x c).toTruncated = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientForwardValueEdgeAtValue_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueEdge_hom,
      SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id]
    exact Iso.inv_hom_id _
  let t := Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hc)
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityTriangleHomotopy_of_faces _ _ _ t.simplex
  · exact t.d₂.trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue_edge e).symm
  · exact t.d₀.trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue_edge d).symm
  · exact t.d₁.trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityIdentity_edge z).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueCancellationHomotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueCancellationHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueCancellationHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueCancellationHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueCancellationHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueCancellationHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientValueCancellationHomotopy._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientValueCancellationHomotopy._proof_6
