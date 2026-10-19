module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessSpace
public import SerrePositivity.InfinityCategories.F1.LiftEndpoint

/-!
概要：表現空間から分類図式と pointed-space の射の族を同時に取り出す。
方針：周囲の四角形空間の二射影を表現空間の包含へ続ける。
規約：可逆な比較は同じ表現空間の頂点同型から取り出す。
使われ方：分類図式の選択独立性と復元の余単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：表現空間全体から分類図式の関手空間への射。
方針：四角形の分類図式への射影へ続ける。
規約：全高次の表現の族を保つ。
使われ方：表現の頂点同型から分類図式の関手同型を得る。 -/
def transportWitnessDiagram {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] :
    transportWitnessSpace p ⟶ (ihom B).obj SpaceInfinity.{u} :=
  transportWitnessSpaceι p ≫ transportSquareDiagram p

/-- 概要：表現空間全体から pointed-space 値の全空間の射の関手空間への射。
方針：四角形の全空間側への射影へ続ける。
規約：分類図式の射影と同じ表現の族を使う。
使われ方：比較射の選択独立性。 -/
def transportWitnessPointed {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] :
    transportWitnessSpace p ⟶ (ihom E).obj PointedSpaceInfinity.{u} :=
  transportWitnessSpaceι p ≫ transportSquarePointed p

/-- 概要：分類図式の族の頂点は実際の表現の分類図式。
方針：四角形の分類図式の頂点公式を使う。
規約：頂点の厳密な等式。
使われ方：選択した表現の分類図式への比較。 -/
lemma transportWitnessDiagram_vertex {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (R : LeftTransportRepresentation p) :
    (transportWitnessDiagram p).app _ (transportWitnessVertex R) = functorVertex R.diagram := by
  exact transportSquareVertex_diagram R.toSquare

/-- 概要：pointed-space の族の頂点は実際の表現の全空間の射。
方針：四角形の全空間側の頂点公式を使う。
規約：分類図式と同じ表現を評価する。
使われ方：比較射の関手同型への移送。 -/
lemma transportWitnessPointed_vertex {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (R : LeftTransportRepresentation p) :
    (transportWitnessPointed p).app _ (transportWitnessVertex R) = functorVertex R.pointedMap := by
  exact transportSquareVertex_pointed R.toSquare

/-- 概要：表現の二つの族は普遍射影への合成で厳密に可換。
方針：四角形空間の二射影の可換条件を表現空間で前合成する。
規約：全高次のデータの等式。
使われ方：分類図式と全空間比較を同時に保つ。 -/
lemma transportWitnessDiagram_condition {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] :
    transportWitnessPointed p ≫ (ihom E).map pointedSpaceProjection =
      transportWitnessDiagram p ≫ (pre p).app SpaceInfinity := by
  dsimp only [transportWitnessPointed, transportWitnessDiagram]
  rw [Category.assoc, transportSquareSpace_condition, Category.assoc]

/-- 概要：表現空間内の頂点同型は実際の分類図式の関手同型を与える。
方針：分類図式の族で頂点同型を写す。
規約：この構成自体に小ささは不要。
使われ方：coherent な分類図式の選択独立性と余単位。 -/
def LeftTransportRepresentation.diagramIso {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S : LeftTransportRepresentation p)
    (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    FunctorIso R.diagram S.diagram :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk (transportWitnessDiagram_vertex R))).symm ≪≫
    VertexIso.map h (transportWitnessDiagram p) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk (transportWitnessDiagram_vertex S))

/-- 概要：同じ表現空間内の頂点同型は全空間側の射の関手同型も与える。
方針：pointed-space の族で同じ頂点同型を写す。
規約：分類図式の比較とは独立に選ばない。
使われ方：分類図式の選択と全空間比較の同時の選択独立性。 -/
def LeftTransportRepresentation.pointedIso {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S : LeftTransportRepresentation p)
    (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    FunctorIso R.pointedMap S.pointedMap :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk (transportWitnessPointed_vertex R))).symm ≪≫
    VertexIso.map h (transportWitnessPointed p) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk (transportWitnessPointed_vertex S))

end SerrePositivity.InfinityCategories
