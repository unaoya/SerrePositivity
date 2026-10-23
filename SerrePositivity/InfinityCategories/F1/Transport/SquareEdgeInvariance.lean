module

public import SerrePositivity.InfinityCategories.F1.Transport.SquareRepresentation
public import SerrePositivity.InfinityCategories.F1.Transport.InvertibleLeftTransport

/-!
概要：可逆な分類図式の辺に沿う表現条件の移送。
方針：任意の四角形の辺を fiber の prism に制限し、片端の同値性と可逆 transport を合成する。
規約：新しい終点を最初から表現と仮定しない。
使われ方：Kerodon Lemma 5.6.8.6、表現の選択空間の replete 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：任意の四角形の辺の分類図式側の辺。
方針：底側の射影で写し、厳密な頂点の公式で端点を揃える。
規約：両端の四角形の fiber 条件は不要。
使われ方：Kerodon §5.6.8、片端だけの表現条件の移送。 -/
noncomputable def transportSquareDiagramEdge {E B : SSet.{u + 1}} {p : E ⟶ B}
    {S T : LeftTransportSquare p}
    (e : SSet.Edge (transportSquareVertex S) (transportSquareVertex T)) :
    SSet.Edge (functorVertex S.diagram) (functorVertex T.diagram) :=
  (e.map (transportSquareDiagram p)).ofEq (transportSquareVertex_diagram S)
    (transportSquareVertex_diagram T)

/-- 概要：任意の四角形の辺の全空間側の辺。
方針：pointed space 値の射影で写し、端点を揃える。
規約：表現条件は仮定しない。
使われ方：Kerodon §5.6.8、fiber の prism の構成。 -/
noncomputable def transportSquarePointedEdge {E B : SSet.{u + 1}} {p : E ⟶ B}
    {S T : LeftTransportSquare p}
    (e : SSet.Edge (transportSquareVertex S) (transportSquareVertex T)) :
    SSet.Edge (functorVertex S.pointedMap) (functorVertex T.pointedMap) :=
  (e.map (transportSquarePointed p)).ofEq (transportSquareVertex_pointed S)
    (transportSquareVertex_pointed T)

/-- 概要：任意の四角形の辺の prism は元の底への射と可換。
方針：全次数の引き戻し条件を Yoneda と uncurry の自然性で prism に移す。
規約：片端の四角形の同値性すら要求しない。
使われ方：Kerodon §5.6.8、fiber prism の底側の式。 -/
lemma transportSquarePrism_projection {E B : SSet.{u + 1}} {p : E ⟶ B}
    {S T : LeftTransportSquare p}
    (e : SSet.Edge (transportSquareVertex S) (transportSquareVertex T)) :
    functorEdgePrism (transportSquarePointedEdge e) ≫ pointedSpaceProjection =
      (Δ[1] ◁ p) ≫ functorEdgePrism (transportSquareDiagramEdge e) := by
  unfold functorEdgePrism functorFamilyPrism
  change ((β_ (Δ[1] : SSet.{u + 1}) E).hom ≫
    uncurry (SSet.yonedaEquiv.symm ((transportSquarePointed p).app _ e.edge))) ≫
      pointedSpaceProjection = (Δ[1] ◁ p) ≫ (β_ (Δ[1] : SSet.{u + 1}) B).hom ≫
        uncurry (SSet.yonedaEquiv.symm ((transportSquareDiagram p).app _ e.edge))
  rw [← SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_comp,
    Category.assoc, ← uncurry_natural_right, Category.assoc, transportSquareSpace_condition,
    ← Category.assoc (SSet.yonedaEquiv.symm e.edge), uncurry_pre_app,
    ← Category.assoc, ← BraidedCategory.braiding_naturality_right, Category.assoc]

/-- 概要：四角形の辺の終点の fiber 比較は始点の比較と普遍 transport の合成と関手同型。
方針：四角形の prism を元の射影の fiber に制限する。
規約：両端の比較の同値性を仮定しない。
使われ方：Kerodon §5.6.8、表現条件を新しい終点へ移す比較。 -/
noncomputable def transportSquareFiberPrismIso {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {S T : LeftTransportSquare p}
    (e : SSet.Edge (transportSquareVertex S) (transportSquareVertex T)) (b : B _⦋0⦌) :
    FunctorIso (T.pointedFiberMap b)
      (S.pointedFiberMap b ≫ edgeTransport pointedSpaceProjection
        (functorEdgeAt (transportSquareDiagramEdge e) b)) := by
  let H := (Δ[1] ◁ vertexFiberι p b) ≫ functorEdgePrism (transportSquarePointedEdge e)
  have h₀ : prismEndpoint 0 _ ≫ H = S.pointedFiberMap b ≫
      vertexFiberι pointedSpaceProjection (S.diagram.app _ b) := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, functorEdgePrism_zero,
      S.pointedFiberMap_ι]
  have h₁ : prismEndpoint 1 _ ≫ H = T.pointedFiberMap b ≫
      vertexFiberι pointedSpaceProjection (T.diagram.app _ b) := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, functorEdgePrism_one,
      T.pointedFiberMap_ι]
  have hp : H ≫ pointedSpaceProjection = fst _ _ ≫
      SSet.yonedaEquiv.symm (functorEdgeAt (transportSquareDiagramEdge e) b).edge := by
    dsimp only [H]
    rw [Category.assoc, transportSquarePrism_projection, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, vertexFiberι_comp, functorEdgePrism_const]
    rfl
  exact leftFibrationPrism_transportIso pointedSpaceProjection
    (functorEdgeAt (transportSquareDiagramEdge e) b) (S.pointedFiberMap b) (T.pointedFiberMap b)
    H h₀ h₁ hp

/-- 概要：可逆な分類図式の辺は始点の表現条件を終点へ移す。
方針：始点の fiber 同値と普遍 transport の同値を prism の比較で終点へ移す。
規約：終点が表現であるとは仮定しない。
使われ方：Kerodon Lemma 5.6.8.6、表現空間の可逆な辺に沿う閉性。 -/
lemma LeftTransportSquare.isRepresentation_of_edge {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {S T : LeftTransportSquare p}
    (e : SSet.Edge (transportSquareVertex S) (transportSquareVertex T)) (hS : S.IsRepresentation)
    (he : IsInvertibleEdge (transportSquareDiagramEdge e)) : T.IsRepresentation := by
  intro b
  have hb : IsInvertibleEdge (functorEdgeAt (transportSquareDiagramEdge e) b) :=
    (isInvertibleEdge_congr (show (functorEdgeAt (transportSquareDiagramEdge e) b).edge =
      ((transportSquareDiagramEdge e).toTruncated.map
        ((truncation 2).map (evaluateFunctorAt b))).edge from rfl)).mpr
      (he.map (evaluateFunctorAt b))
  exact ((hS b).comp (edgeTransport_isQCatEquivalence_of_isInvertibleEdge
    pointedSpaceProjection _ hb)).ofFunctorIso (transportSquareFiberPrismIso e b).symm

/-- 概要：表現を表す頂点から可逆な分類図式の辺に沿って進んだ頂点も表現を表す。
方針：終点の四角形を回収し、片端の表現条件から新しい表現を構成する。
規約：周囲の空間の辺の分類図式側の可逆性だけを要求する。
使われ方：Kerodon Lemma 5.6.8.10、制限で持ち上げた一次の辺の終点の検査。 -/
lemma isTransportWitnessVertex_target {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    {x y : (transportSquareSpace p) _⦋0⦌} (e : SSet.Edge x y) (hx : IsTransportWitnessVertex p x)
    (he : IsInvertibleEdge (e.map (transportSquareDiagram p))) : IsTransportWitnessVertex p y := by
  obtain ⟨R, rfl⟩ := hx
  let T := transportSquareOfVertex p y
  let e' : SSet.Edge (transportSquareVertex R.toSquare) (transportSquareVertex T) :=
    e.ofEq rfl (transportSquareVertex_ofVertex p y).symm
  have hd : IsInvertibleEdge (transportSquareDiagramEdge e') :=
    (isInvertibleEdge_congr (show (transportSquareDiagramEdge e').edge =
      (e.map (transportSquareDiagram p)).edge from rfl)).mpr he
  have ht := LeftTransportSquare.isRepresentation_of_edge e' R.toSquare_isRepresentation hd
  refine ⟨T.toRepresentation ht, ?_⟩
  rw [T.toRepresentation_toSquare ht]
  exact transportSquareVertex_ofVertex p y

end SerrePositivity.InfinityCategories
