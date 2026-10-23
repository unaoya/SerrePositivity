module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessDiagram
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismEdgeLifting

/-!
概要：表現空間内の辺から分類図式と全空間側の同時の prism を取り出す。
方針：二射影で辺を写し同じ単体の像として prism の可換条件を得る。
規約：二つの prism を独立に選択しない。
使われ方：復元の比較射と unstraightening の変換への作用を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：表現空間内の辺は分類図式の関手空間の実際の辺を与える。
方針：分類図式への射影で一次単体を写す。
規約：端点は実際の二つの分類図式。
使われ方：unstraightening の変換への作用の入力。 -/
def transportWitnessSpaceDiagramEdge {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    {R S : LeftTransportRepresentation p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (transportWitnessSpace p))
      (transportWitnessVertex R) (transportWitnessVertex S)) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj SpaceInfinity))
      (functorVertex R.diagram) (functorVertex S.diagram) where
  edge := (transportWitnessDiagram p).app _ e.edge
  src_eq := (e.map ((truncation 2).map (transportWitnessDiagram p))).src_eq.trans
    (transportWitnessDiagram_vertex R)
  tgt_eq := (e.map ((truncation 2).map (transportWitnessDiagram p))).tgt_eq.trans
    (transportWitnessDiagram_vertex S)

/-- 概要：同じ表現空間内の辺は全空間側の関手空間の実際の辺も与える。
方針：pointed-space の射影で同じ一次単体を写す。
規約：分類図式の辺と同じ表現の辺を使う。
使われ方：変換の prism の具体的な持ち上げ。 -/
def transportWitnessSpacePointedEdge {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    {R S : LeftTransportRepresentation p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (transportWitnessSpace p))
      (transportWitnessVertex R) (transportWitnessVertex S)) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom E).obj PointedSpaceInfinity))
      (functorVertex R.pointedMap) (functorVertex S.pointedMap) where
  edge := (transportWitnessPointed p).app _ e.edge
  src_eq := (e.map ((truncation 2).map (transportWitnessPointed p))).src_eq.trans
    (transportWitnessPointed_vertex R)
  tgt_eq := (e.map ((truncation 2).map (transportWitnessPointed p))).tgt_eq.trans
    (transportWitnessPointed_vertex S)

/-- 概要：関手空間の後合成を prism へ移す。
方針：uncurry の後合成則を使う。
規約：パラメーター空間に制限はない。
使われ方：同時の二つの prism の可換性。 -/
lemma functorFamilyPrism_post {K A X Y : SSet.{u}} (q : K ⟶ (ihom A).obj X) (f : X ⟶ Y) :
    functorFamilyPrism (q ≫ (ihom A).map f) = functorFamilyPrism q ≫ f := by
  simp only [functorFamilyPrism, uncurry_natural_right, Category.assoc]

/-- 概要：分類図式と全空間側の辺の prism は普遍射影への合成で厳密に可換。
方針：同じ一次単体で表現空間の可換条件を評価し prism へ移す。
規約：底上のホモトピーも含む全ての射が厳密に可換。
使われ方：unstraightening の具体的な持ち上げとして表現の辺を使う。 -/
lemma transportWitnessSpaceEdgePrism_condition {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    {R S : LeftTransportRepresentation p}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (transportWitnessSpace p))
      (transportWitnessVertex R) (transportWitnessVertex S)) :
    functorEdgePrism (transportWitnessSpacePointedEdge e) ≫ pointedSpaceProjection =
      (Δ[1] ◁ p) ≫ functorEdgePrism (transportWitnessSpaceDiagramEdge e) := by
  let q : (Δ[1] : SSet.{u + 1}) ⟶ transportWitnessSpace p := SSet.yonedaEquiv.symm e.edge
  have h := congrArg (fun f ↦ q ≫ f) (transportWitnessDiagram_condition p)
  simp only [← Category.assoc] at h
  have h' := congrArg functorFamilyPrism h
  rw [functorFamilyPrism_post, functorFamilyPrism_pre] at h'
  dsimp only [functorEdgePrism, transportWitnessSpacePointedEdge, transportWitnessSpaceDiagramEdge]
  change functorFamilyPrism (SSet.yonedaEquiv.symm
      ((transportWitnessPointed p).app (Opposite.op ⦋1⦌) e.edge)) ≫ pointedSpaceProjection =
    (Δ[1] ◁ p) ≫ functorFamilyPrism (SSet.yonedaEquiv.symm
      ((transportWitnessDiagram p).app (Opposite.op ⦋1⦌) e.edge))
  simpa only [q, SSet.yonedaEquiv_symm_comp] using h'

end SerrePositivity.InfinityCategories
