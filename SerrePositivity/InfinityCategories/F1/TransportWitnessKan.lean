module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessEdges
public import SerrePositivity.InfinityCategories.F1B.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：空間値 transport witnesses は Kan 複体。
方針：表現の辺を底の各 fiber で比較し、全辺の可逆性から Kan 性を得る。
規約：非空性と可縮性を仮定しない。基底の quasicategory 性も不要。
使われ方：Kerodon Lemma 5.6.8.7、表現空間の制限の全ホーン持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同じ left fibration の二つの表現を結ぶ四角形の辺は可逆。
方針：分類図式の辺を対象ごとの可逆性で判定し、left fibration で反映する。
規約：元の底 B は任意の単体集合。
使われ方：Kerodon §5.6.8、transport witnesses の辺の可逆性。 -/
lemma transportSquareEdge_isInvertible {E B : SSet.{u + 1}} {p : E ⟶ B}
    [LeftFibration p] {R S : LeftTransportRepresentation p}
    (e : SSet.Edge (transportSquareVertex R.toSquare) (transportSquareVertex S.toSquare)) :
    IsInvertibleEdge e := by
  have hd : IsInvertibleEdge (transportWitnessDiagramEdge e) := by
    apply (isInvertibleEdge_iff_evaluateFunctorAt (transportWitnessDiagramEdge e).toTruncated).mpr
    intro b
    exact (isInvertibleEdge_congr
      (show (functorEdgeAt (transportWitnessDiagramEdge e) b).edge =
        ((transportWitnessDiagramEdge e).toTruncated.map
          ((truncation 2).map (evaluateFunctorAt b))).edge from rfl)).mp
      (transportWitnessDiagramEdge_at_isInvertible e b)
  apply leftFibration_reflects_invertibleEdge (transportSquareDiagram p) e.toTruncated
  exact (isInvertibleEdge_congr
    (show (transportWitnessDiagramEdge e).edge =
      (e.toTruncated.map ((truncation 2).map (transportSquareDiagram p))).edge from rfl)).mp hd

/-- 概要：transport witnesses の全ての辺は可逆。
方針：両端の表現を頂点対応で回収し、全部分複体の包含の充満忠実性を使う。
規約：辺自体に可逆性の条件を追加しない。
使われ方：Kerodon Lemma 5.6.8.7、選択空間の亜群性。 -/
lemma transportWitnessEdge_isInvertible {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    {x y : (transportWitnessSpace p) _⦋0⦌} (e : SSet.Edge x y) : IsInvertibleEdge e := by
  obtain ⟨R, rfl⟩ := transportWitnessVertex_surjective p x
  obtain ⟨S, rfl⟩ := transportWitnessVertex_surjective p y
  apply (isFullyFaithful_fullSubcomplexOnVertices_ι
    (transportSquareSpace p) (IsTransportWitnessVertex p)).reflects_isInvertibleEdge e.toTruncated
  exact transportSquareEdge_isInvertible (e.map (transportWitnessSpaceι p))

/-- 概要：任意の left fibration の空間値 transport witnesses は Kan 複体。
方針：全てのホモトピー圏の射を辺で表し、全辺の可逆性から Kan 性を得る。
規約：表現の存在や小ささを仮定せず、空の選択空間も許す。
使われ方：Kerodon Lemma 5.6.8.7、相対表現の延長のホーン充填の入力。 -/
instance transportWitnessSpace_kanComplex {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] : KanComplex (transportWitnessSpace p) := by
  have hg : IsGroupoid (hoFunctor.obj (transportWitnessSpace p)) := by
    constructor
    intro a b f
    obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective (X := transportWitnessSpace p) a b f
    exact transportWitnessEdge_isInvertible p (SSet.Edge.ofTruncated e)
  exact kanComplex_of_isGroupoid _

end SerrePositivity.InfinityCategories
