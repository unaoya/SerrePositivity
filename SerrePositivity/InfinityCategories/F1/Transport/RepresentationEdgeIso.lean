module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationComparisonCoherence
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessPrism
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEdgeFromPrism

/-!
概要：表現空間の辺を頂点同型として扱い、その分類図式の実際の辺と比較する。
方針：表現空間の Kan 性とホモトピー圏の射の像を使う。
規約：同じ辺そのものから比較を作る。
使われ方：選択した単位変換と余単位の逆の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：表現空間の任意の辺は両表現の頂点同型を与える。
方針：Kan 複体のホモトピー圏の亜群性を使う。
規約：元の辺の生成する射そのものを順方向に使う。
使われ方：具体的な単位の辺を選択した余単位と比較する。 -/
def transportWitnessSpaceEdgeIso {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    {R S : LeftTransportRepresentation p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (transportWitnessSpace p))
      (transportWitnessVertex R) (transportWitnessVertex S)) :
    VertexIso (transportWitnessVertex R) (transportWitnessVertex S) := by
  have : IsGroupoid (hoFunctor.obj (transportWitnessSpace p)) := kanComplex_ho_isGroupoid _
  let f : (SSet.HomotopyCategory.mk (transportWitnessVertex R) :
      hoFunctor.obj (transportWitnessSpace p)) ⟶
      SSet.HomotopyCategory.mk (transportWitnessVertex S) :=
    SSet.Truncated.HomotopyCategory.homMk e
  have : IsIso f := IsGroupoid.all_isIso (C := hoFunctor.obj (transportWitnessSpace p)) f
  exact asIso f

/-- 概要：分類図式の実際の辺の射は表現の辺の頂点同型の像。
方針：辺の一次単体の一致を端点の移送を含めてホモトピー圏へ写す。
規約：別の同型な辺への取り替えを行わない。
使われ方：指定した単位変換の射そのものを同定する。 -/
lemma transportWitnessSpaceDiagramEdge_hom {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {R S : LeftTransportRepresentation p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (transportWitnessSpace p))
      (transportWitnessVertex R) (transportWitnessVertex S)) :
    SSet.Truncated.HomotopyCategory.homMk (transportWitnessSpaceDiagramEdge e) =
      (R.diagramIso S (transportWitnessSpaceEdgeIso e)).hom := by
  have ha := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    (transportWitnessSpaceDiagramEdge e)
    (e.map ((truncation 2).map (transportWitnessDiagram p))) rfl
  obtain ⟨hx, hy, he⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha
  simpa [LeftTransportRepresentation.diagramIso, VertexIso.map, transportWitnessSpaceEdgeIso,
    SSet.mapHomotopyCategory, SSet.Truncated.mapHomotopyCategory_homMk] using he

/-- 概要：小さい次数 fiber の辺の頂点同型は同じ表現間の選択した比較と一致する。
方針：可縮な表現空間の頂点同型の一意性を使う。
規約：一致は表現の比較を忘れる前に証明する。
使われ方：単位の辺の同型と余単位の逆を同定する。 -/
lemma transportWitnessSpaceEdgeIso_eq {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] (hp : HasSmallSimplexFibers p) {R S : LeftTransportRepresentation p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (transportWitnessSpace p))
      (transportWitnessVertex R) (transportWitnessVertex S))
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    transportWitnessSpaceEdgeIso e = a :=
  smallFiberTransportRepresentationVertexIso_unique p hp R S _ _

/-- 概要：関手空間の辺を prism にしてから回収すると元の辺そのものとなる。
方針：prism の単射性と回収後の prism の一致を使う。
規約：端点の証明の違いは辺の等式に影響しない。
使われ方：単位変換の prism とその実際の辺を厳密に結ぶ。 -/
lemma functorEdgeFromPrism_edgePrism {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (functorVertex F) (functorVertex G)) :
    functorEdgeFromPrism (functorEdgePrism e) (functorEdgePrism_zero e)
      (functorEdgePrism_one e) = e := by
  apply SSet.Truncated.Edge.ext
  apply (SSet.yonedaEquiv (X := (ihom B).obj X) (n := ⦋1⦌)).symm.injective
  apply functorFamilyPrism_injective Δ[1] B X
  exact functorEdgeFromPrism_prism (functorEdgePrism e) _ _

end SerrePositivity.InfinityCategories
