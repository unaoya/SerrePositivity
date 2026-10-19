module

public import SerrePositivity.InfinityCategories.F1.CoherentStraighteningUnitTransformation
public import SerrePositivity.InfinityCategories.F1.TransportRepresentationEdgeIso

/-!
概要：指定した単位変換の実際の射を選択した余単位の逆と同定する。
方針：可縮な表現空間で単位の辺と余単位の逆を比較し同じ図式射影で写す。
規約：同型な別の単位変換へ取り替えない。
使われ方：単位・余単位の自然性と三角恒等式の成分をそろえる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した単位の表現空間内の辺から得る図式の関手同型。
方針：同じ辺の頂点同型を分類図式へ写す。
規約：順方向の射は指定した辺の像。
使われ方：単位変換の可逆性と余単位との比較。 -/
def coherentStraighteningUnitIso {B : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso F (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection_hasSmallSimplexFibers F)) :=
  (unstraighteningTransportRepresentation F).diagramIso
    (smallFiberLeftStraighteningRepresentation (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection_hasSmallSimplexFibers F))
    (transportWitnessSpaceEdgeIso (coherentStraighteningUnitWitnessEdge F))

/-- 概要：指定した単位の辺による同型は選択した余単位の逆そのもの。
方針：表現空間内の頂点同型の一意性を図式射影へ写す。
規約：図式の関手同型の実際の等式。
使われ方：単位と余単位の比較を同じ選択にそろえる。 -/
lemma coherentStraighteningUnitIso_eq_counit_symm {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    coherentStraighteningUnitIso F = (coherentStraighteningCounit F).symm := by
  let R := smallFiberLeftStraighteningRepresentation (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F)
  let S := unstraighteningTransportRepresentation F
  let a := smallFiberTransportRepresentationVertexIso (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F) R S
  have he := transportWitnessSpaceEdgeIso_eq (leftUnstraighteningProjection_hasSmallSimplexFibers F)
    (coherentStraighteningUnitWitnessEdge F) a.symm
  change S.diagramIso R (transportWitnessSpaceEdgeIso (coherentStraighteningUnitWitnessEdge F)) =
    (R.diagramIso S a).symm
  rw [he]
  exact R.diagramIso_symm S a

/-- 概要：単位変換の prism の実際の辺が生成する射は単位同型の順方向の射。
方針：prism の往復で元の辺を回収し表現空間の辺の像の公式を使う。
規約：指定した変換そのものの射を扱う。
使われ方：単位変換の可逆性を検証する。 -/
lemma coherentStraighteningUnitTransformation_edge_hom {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeFromPrism
      (coherentStraighteningUnitTransformation F) (coherentStraighteningUnitTransformation_zero F)
      (coherentStraighteningUnitTransformation_one F)) = (coherentStraighteningUnitIso F).hom := by
  change SSet.Truncated.HomotopyCategory.homMk (functorEdgeFromPrism
    (functorEdgePrism (transportWitnessSpaceDiagramEdge (coherentStraighteningUnitWitnessEdge F)))
    (functorEdgePrism_zero _) (functorEdgePrism_one _)) = _
  rw [functorEdgeFromPrism_edgePrism]
  exact transportWitnessSpaceDiagramEdge_hom (coherentStraighteningUnitWitnessEdge F)

/-- 概要：指定した単位変換の実際の射は余単位の逆射。
方針：単位の辺の射と余単位の逆同型の順方向の射を同定する。
規約：単なる同値の存在に弱めない。
使われ方：単位変換と余単位の成分の整合性。 -/
lemma coherentStraighteningUnitTransformation_eq_counit_inv {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeFromPrism
      (coherentStraighteningUnitTransformation F) (coherentStraighteningUnitTransformation_zero F)
      (coherentStraighteningUnitTransformation_one F)) = (coherentStraighteningCounit F).inv := by
  rw [coherentStraighteningUnitTransformation_edge_hom, coherentStraighteningUnitIso_eq_counit_symm]
  rfl

/-- 概要：指定した単位変換の辺そのものは可逆。
方針：実際の辺の射を構成した単位同型の順方向の射へ戻す。
規約：元の変換の辺を取り替えない。
使われ方：単位による分類図式の同値性。 -/
lemma coherentStraighteningUnitTransformation_isInvertible {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    IsInvertibleEdge (functorEdgeFromPrism
      (coherentStraighteningUnitTransformation F) (coherentStraighteningUnitTransformation_zero F)
      (coherentStraighteningUnitTransformation_one F)) := by
  change IsIso _
  rw [coherentStraighteningUnitTransformation_edge_hom]
  infer_instance

end SerrePositivity.InfinityCategories
