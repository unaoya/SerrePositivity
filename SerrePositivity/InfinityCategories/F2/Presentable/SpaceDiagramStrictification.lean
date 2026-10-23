module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.Transport.NerveTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningOppositeComparison

/-!
概要：任意の通常の小圏上の coherent な空間値図式を、同じ添字の strict Kan 図式へ移す。
方針：元の小さい unstraightening の strict transport に、実際の分類の余単位と表現比較を合成する。
規約：底全体の一つの関手同型を与える。値ごとの同値の選択では代用しない。
使われ方：錐形状と filtered 添字の共同図式を一度に strict 化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {I : Type u} [SmallCategory I]

/-- 元の小さい復元に対する、同じ添字上の strict Kan 値 transport 図式。 -/
def spaceDiagramStrictification
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    I ⥤ KanObject.{u} :=
  leftStrictTransportFunctor (smallLeftUnstraighteningProjection F)

/-- 同じ strict transport の coherent 実現は、元の図式全体と関手同型。 -/
def spaceDiagramStrictificationIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    FunctorIso (kanDiagramCoherentNerve (spaceDiagramStrictification F)) F :=
  leftStraighteningCoherentMap_oppositeVertexIso (smallLeftUnstraighteningProjection F) ≪≫
    (leftStraighteningInfinityDiagram_representationIso (smallLeftUnstraighteningProjection F)
      (nerveLeftTransportRepresentation (smallLeftUnstraighteningProjection F))).symm ≪≫
    leftStraighteningInfinityCounit F

end SerrePositivity.InfinityCategories.F2.Presentable
