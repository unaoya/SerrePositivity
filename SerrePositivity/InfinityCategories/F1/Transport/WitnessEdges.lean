module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessSpace
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationPrismTransport
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismFiber

/-!
概要：同じ left fibration の二つの表現の間の四角形の辺を比較する。
方針：各 fiber 上の prism を標準 transport と比較し、端点の同値性で可逆性を検出する。
規約：表現の辺に追加の可逆性条件を課さない。
使われ方：Kerodon §5.6.8、transport witnesses の Kan 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：表現の各 fiber から普遍 pointed-space 射影の fiber への比較。
方針：表現の fiber 比較に unstraightening の fiber の標準同型を合成する。
規約：分類図式の指定した頂点上で比較する。
使われ方：Kerodon §5.6.8、表現の辺の transport の同値判定。 -/
noncomputable def LeftTransportRepresentation.pointedFiberMap {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p) (b : B _⦋0⦌) :
    vertexFiber p b ⟶ vertexFiber pointedSpaceProjection (R.diagram.app _ b) :=
  vertexFiberMap p (leftUnstraighteningProjection R.diagram) R.comparison R.over_base b ≫
    (leftUnstraighteningFiberIso R.diagram b).hom

/-- 概要：普遍 fiber への比較の包含は表現の全空間の射の制限。
方針：fiber 同型と底上の比較の包含公式を使う。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon §5.6.8、表現の辺の prism の端点。 -/
lemma LeftTransportRepresentation.pointedFiberMap_ι {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p) (b : B _⦋0⦌) :
    R.pointedFiberMap b ≫ vertexFiberι pointedSpaceProjection (R.diagram.app _ b) =
      vertexFiberι p b ≫ R.pointedMap := by
  rw [LeftTransportRepresentation.pointedFiberMap, Category.assoc]
  change _ ≫ (vertexFiberPullbackIso pointedSpaceProjection R.diagram b).hom ≫ _ = _
  rw [vertexFiberPullbackIso_hom_ι, ← Category.assoc]
  change (vertexFiberMap p (leftUnstraighteningProjection R.diagram) R.comparison R.over_base b ≫
    vertexFiberι (leftUnstraighteningProjection R.diagram) b) ≫
      pullback.fst pointedSpaceProjection R.diagram = _
  rw [vertexFiberMap_ι, Category.assoc]
  rfl

/-- 概要：表現から普遍 pointed-space fiber への比較は同値。
方針：表現の fiber 同値と標準 fiber 同型を合成する。
規約：全頂点で同じ表現の実際の比較を使う。
使われ方：Kerodon §5.6.8、prism の両端の同値性。 -/
lemma LeftTransportRepresentation.pointedFiberMap_isQCatEquivalence {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R : LeftTransportRepresentation p) (b : B _⦋0⦌) :
    IsQCatEquivalence (R.pointedFiberMap b) :=
  (R.fiber_equivalence b).comp
    (qCatEquivalenceOfIso (leftUnstraighteningFiberIso R.diagram b)).isQCatEquivalence

/-- 概要：表現の四角形の辺から分類図式の辺を取り出す。
方針：底側の射影で写し、頂点の公式で端点を揃える。
規約：端点は元の分類図式の関手頂点。
使われ方：Kerodon §5.6.8、表現の辺の可逆性の底側での判定。 -/
noncomputable def transportWitnessDiagramEdge {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {R S : LeftTransportRepresentation p}
    (e : SSet.Edge (transportSquareVertex R.toSquare) (transportSquareVertex S.toSquare)) :
    SSet.Edge (functorVertex R.diagram) (functorVertex S.diagram) :=
  (e.map (transportSquareDiagram p)).ofEq (transportSquareVertex_diagram R.toSquare)
    (transportSquareVertex_diagram S.toSquare)

/-- 概要：表現の四角形の辺から全空間の pointed space 値図式の辺を取り出す。
方針：全空間側の射影で写し、端点を揃える。
規約：実際の全空間の射を端点に持つ。
使われ方：Kerodon §5.6.8、fiber 上の比較 prism の構成。 -/
noncomputable def transportWitnessPointedEdge {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {R S : LeftTransportRepresentation p}
    (e : SSet.Edge (transportSquareVertex R.toSquare) (transportSquareVertex S.toSquare)) :
    SSet.Edge (functorVertex R.pointedMap) (functorVertex S.pointedMap) :=
  (e.map (transportSquarePointed p)).ofEq (transportSquareVertex_pointed R.toSquare)
    (transportSquareVertex_pointed S.toSquare)

/-- 概要：表現の辺の二つの prism は元の射影 p を介して厳密に可換。
方針：四角形の空間の全次数の可換式を一単体の評価で使う。
規約：辺の可逆性は仮定しない。
使われ方：Kerodon §5.6.8、fiber 上の prism が分類図式の辺を被覆する条件。 -/
lemma transportWitnessPrism_projection {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {R S : LeftTransportRepresentation p}
    (e : SSet.Edge (transportSquareVertex R.toSquare) (transportSquareVertex S.toSquare)) :
    functorEdgePrism (transportWitnessPointedEdge e) ≫ pointedSpaceProjection =
      (Δ[1] ◁ p) ≫ functorEdgePrism (transportWitnessDiagramEdge e) := by
  unfold functorEdgePrism functorFamilyPrism
  change ((β_ (Δ[1] : SSet.{u + 1}) E).hom ≫
    uncurry (SSet.yonedaEquiv.symm ((transportSquarePointed p).app _ e.edge))) ≫
      pointedSpaceProjection = (Δ[1] ◁ p) ≫ (β_ (Δ[1] : SSet.{u + 1}) B).hom ≫
        uncurry (SSet.yonedaEquiv.symm ((transportSquareDiagram p).app _ e.edge))
  rw [← SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_comp,
    Category.assoc, ← uncurry_natural_right, Category.assoc, transportSquareSpace_condition,
    ← Category.assoc (SSet.yonedaEquiv.symm e.edge), uncurry_pre_app,
    ← Category.assoc, ← BraidedCategory.braiding_naturality_right, Category.assoc]

/-- 概要：表現の辺を底の一点で評価すると可逆な空間の辺。
方針：fiber の二つの同値を結ぶ prism と標準 transport の同型を比較する。
規約：底 B の quasicategory 性は不要。
使われ方：Kerodon §5.6.8、選択空間の全ての辺の可逆性。 -/
lemma transportWitnessDiagramEdge_at_isInvertible {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {R S : LeftTransportRepresentation p}
    (e : SSet.Edge (transportSquareVertex R.toSquare) (transportSquareVertex S.toSquare))
    (b : B _⦋0⦌) : IsInvertibleEdge (functorEdgeAt (transportWitnessDiagramEdge e) b) := by
  let H := (Δ[1] ◁ vertexFiberι p b) ≫ functorEdgePrism (transportWitnessPointedEdge e)
  have h₀ : prismEndpoint 0 _ ≫ H = R.pointedFiberMap b ≫
      vertexFiberι pointedSpaceProjection (R.diagram.app _ b) := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, functorEdgePrism_zero,
      R.pointedFiberMap_ι]
  have h₁ : prismEndpoint 1 _ ≫ H = S.pointedFiberMap b ≫
      vertexFiberι pointedSpaceProjection (S.diagram.app _ b) := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, functorEdgePrism_one,
      S.pointedFiberMap_ι]
  have hp : H ≫ pointedSpaceProjection = fst _ _ ≫
      SSet.yonedaEquiv.symm (functorEdgeAt (transportWitnessDiagramEdge e) b).edge := by
    dsimp only [H]
    rw [Category.assoc, transportWitnessPrism_projection, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, vertexFiberι_comp, functorEdgePrism_const]
    rfl
  have h := leftFibrationPrism_transportIso pointedSpaceProjection
    (functorEdgeAt (transportWitnessDiagramEdge e) b)
    (R.pointedFiberMap b) (S.pointedFiberMap b) H h₀ h₁ hp
  apply pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence
  exact (R.pointedFiberMap_isQCatEquivalence b).cancel_left
    ((S.pointedFiberMap_isQCatEquivalence b).ofFunctorIso h)

end SerrePositivity.InfinityCategories
