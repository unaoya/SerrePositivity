module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientValueEdge
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpaceTriangleFaces

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- 概要：元の実比較辺と既存指定値比較辺の合成は、同じ Kan 値の恒等とホモトピック。
方針：指定値同型の両逆を実三角形へ読み戻し、その同じ三辺の Kan 射を評価する。
規約：辺を別の代表へ選び直さず、実三角形だけを選ぶ。
使われ方：全固定 fiber 回収の元の値座標での正規化。 -/
def weakSpanKanQuotientValueCancellationHomotopy :
    SSet.Homotopy
      (𝟙 (spaceInfinityObject (spaceInfinityVertex ((weakSpanKanDiagram i x).obj c))).obj)
      (F2.spaceInfinityEdgeValue (weakSpanKanQuotientForwardValueEdgeAtValue h x c) ≫
        F2.spaceInfinityEdgeValue (weakSpanKanQuotientValueEdge h x c)) := by
  let e := weakSpanKanQuotientForwardValueEdgeAtValue h x c
  let d := weakSpanKanQuotientValueEdge h x c
  let z := spaceInfinityVertex ((weakSpanKanDiagram i x).obj c)
  have hc : Truncated.HomotopyCategory.homMk e.toTruncated ≫
      Truncated.HomotopyCategory.homMk d.toTruncated =
      Truncated.HomotopyCategory.homMk (SSet.Edge.id z).toTruncated := by
    change Truncated.HomotopyCategory.homMk
      (weakSpanKanQuotientForwardValueEdgeAtValue h x c).toTruncated ≫
      Truncated.HomotopyCategory.homMk (weakSpanKanQuotientValueEdge h x c).toTruncated = _
    rw [weakSpanKanQuotientForwardValueEdgeAtValue_hom, weakSpanKanQuotientValueEdge_hom,
      SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id]
    exact Iso.inv_hom_id _
  let t := Classical.choice (compStruct_nonempty_of_homMk_fac hc)
  apply F2.spaceInfinityTriangleHomotopy_of_faces _ _ _ t.simplex
  · exact t.d₂.trans (F2.spaceInfinityEdgeValue_edge e).symm
  · exact t.d₀.trans (F2.spaceInfinityEdgeValue_edge d).symm
  · exact t.d₁.trans (F2.spaceInfinityIdentity_edge z).symm

end SerrePositivity.KST.Fibration
