module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.EssentiallySmallStraightening
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessDiagram

/-!
概要：元の全空間の二つの実際の表現の、分類図式と全空間側の同時の選択独立性。
方針：一つの表現の存在から fiber の小さい模型を回収し、同じ可縮表現空間で比較する。
規約：次数 fiber の小ささも表現の比較の追加仮定も不要。
使われ方：相対普遍性の空間値版の一意性と、底変換での分類図式の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ射影の実際の二つの表現は、同じ表現空間内の頂点同型で比較できる。 -/
def LeftTransportRepresentation.canonicalVertexIso {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S : LeftTransportRepresentation p) :
    VertexIso (transportWitnessVertex R) (transportWitnessVertex S) :=
  (essentiallySmallTransportWitnessSpace_isContractibleKan
    p R.hasEssentiallySmallFibers).vertexIso _ _

/-- 同じ射影の二つの実際の分類図式は、全パラメーターで関手同型となる。 -/
def LeftTransportRepresentation.canonicalDiagramIso {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S : LeftTransportRepresentation p) :
    FunctorIso R.diagram S.diagram :=
  R.diagramIso S (R.canonicalVertexIso S)

/-- 同じ比較を全空間側へ写すと、元の pointed-space への二射も関手同型となる。 -/
def LeftTransportRepresentation.canonicalPointedIso {E B : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (R S : LeftTransportRepresentation p) :
    FunctorIso R.pointedMap S.pointedMap :=
  R.pointedIso S (R.canonicalVertexIso S)

local instance essentiallySmallComparisonPullbackSndLF {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 同値不変な小さい fiber による分類図式は、任意の底変換と関手同型で両立する。 -/
def essentiallySmallLeftStraighteningBaseChangeIso {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p) (g : D ⟶ B) :
    FunctorIso
      (essentiallySmallLeftStraighteningDiagram (pullback.snd p g) (hp.pullback_snd g))
      (g ≫ essentiallySmallLeftStraighteningDiagram p hp) :=
  (essentiallySmallLeftStraighteningRepresentation
    (pullback.snd p g) (hp.pullback_snd g)).canonicalDiagramIso
    ((essentiallySmallLeftStraighteningRepresentation p hp).restrict g)

end SerrePositivity.InfinityCategories
