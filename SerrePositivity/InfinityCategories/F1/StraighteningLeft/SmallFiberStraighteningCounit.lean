module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallFiberStraightening
public import SerrePositivity.InfinityCategories.F1.Coherent.RepresentationExtension
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessDiagram

/-!
概要：次数 fiber が小さい表現の選択独立性と coherent な図式の復元の余単位。
方針：可縮な表現空間内の頂点同型を分類図式と pointed-space の射に同時に写す。
規約：対象ごとの余単位であり全図式にわたる自然性は別途証明する。
使われ方：unstraightening と分類図式の一般の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

local instance smallFiberCounitPullbackSndLF {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) : LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：次数 fiber が小さい任意の二つの表現を同じ可縮空間内で比較する。
方針：表現空間の可縮性から頂点同型を取る。
規約：分類図式と全空間側の比較に同じ同型を使う。
使われ方：復元の余単位と底変換の比較。 -/
def smallFiberTransportRepresentationVertexIso {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasSmallSimplexFibers p)
    (R S : LeftTransportRepresentation p) :
    VertexIso (transportWitnessVertex R) (transportWitnessVertex S) :=
  (smallFiberTransportWitnessSpace_isContractibleKan p hp).vertexIso _ _

/-- 概要：次数 fiber が小さい二つの分類図式は関手同型。
方針：同じ表現空間の頂点同型を分類図式へ写す。
規約：辺ごとの一致だけから図式の同型を推論しない。
使われ方：任意の coherent な分類図式の選択独立性。 -/
def smallFiberTransportRepresentationDiagramIso {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasSmallSimplexFibers p)
    (R S : LeftTransportRepresentation p) : FunctorIso R.diagram S.diagram :=
  R.diagramIso S (smallFiberTransportRepresentationVertexIso p hp R S)

/-- 概要：同じ比較は全空間から pointed-space への二射の関手同型を与える。
方針：分類図式の比較と同じ頂点同型を全空間側へ写す。
規約：二つの射の比較を独立に選ばない。
使われ方：分類図式の選択と全空間比較の整合性。 -/
def smallFiberTransportRepresentationPointedIso {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasSmallSimplexFibers p)
    (R S : LeftTransportRepresentation p) : FunctorIso R.pointedMap S.pointedMap :=
  R.pointedIso S (smallFiberTransportRepresentationVertexIso p hp R S)

/-- 概要：任意の底上の coherent な図式は unstraightening の分類から関手同型で戻る。
方針：選んだ表現と元の図式による標準表現を可縮な表現空間内で比較する。
規約：対象ごとの余単位であり関手全体の自然性はまだ含めない。
使われ方：coherent な分類の一般の余単位の成分。 -/
def coherentStraighteningCounit {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso (smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection_hasSmallSimplexFibers F)) F :=
  smallFiberTransportRepresentationDiagramIso (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection_hasSmallSimplexFibers F)
    (smallFiberLeftStraighteningRepresentation (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection_hasSmallSimplexFibers F))
    (unstraighteningTransportRepresentation F)

/-- 概要：分類図式の底変換は底変換した射影の分類図式と関手同型。
方針：選んだ表現と元の選んだ表現の制限を同じ表現空間内で比較する。
規約：底変換する底の小ささを要求しない。
使われ方：分類の底変換との整合性の成分。 -/
def smallFiberLeftStraighteningBaseChangeIso {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasSmallSimplexFibers p) (g : D ⟶ B) :
    FunctorIso (smallFiberLeftStraighteningDiagram (pullback.snd p g) (hp.pullback_snd g))
      (g ≫ smallFiberLeftStraighteningDiagram p hp) :=
  smallFiberTransportRepresentationDiagramIso (pullback.snd p g) (hp.pullback_snd g)
    (smallFiberLeftStraighteningRepresentation (pullback.snd p g) (hp.pullback_snd g))
    ((smallFiberLeftStraighteningRepresentation p hp).restrict g)

end SerrePositivity.InfinityCategories
