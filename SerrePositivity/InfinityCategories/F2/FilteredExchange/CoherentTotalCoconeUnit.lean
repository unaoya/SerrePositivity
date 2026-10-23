module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeRealizationTransformation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.YonedaHomotopyVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalCocone

/-!
概要：構成した native 全空間余錐の標準比較の像を元の実際の単位と比較する。
方針：実現の比較を変換空間へ戻し、元の単位の表現同型と合成する。
規約：指定図式・余錐・頂点・単位を保持する。
使われ方：全 Hom の余極限判定で使う単位の追跡。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：native 全空間余錐の比較の像は元の全空間の単位と同型。
方針：両端固定の実現比較を写し、元の単位を表す選択済みの同型と続ける。
規約：全空間の実際の単位。使われ方：余錐の全 Hom 普遍性の単位整合。 -/
def coherentTotalCoconeUnitIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (smallLeftUnstraightening F)).obj
        (spaceInfinityObject (coherentDiagramTotalVertex F)).obj))
      ((coherentCoconeTotalComparison F (coherentDiagramTotalVertex F)).app (Opposite.op ⦋0⦌)
        (coconeMappingPointAt (coherentDiagramTotalCocone F) (coherentDiagramTotalVertex F)
          (coherentDiagramTotalCocone_vertex F)))
      (ULift.up.{u + 1, u} (functorVertex (coherentDiagramTotalUnit F))) := by
  let H := coconeRealizationTransformationHomotopy
    (coherentTotalUnitRepresentation F).1 (coherentTotalCoconeRealization F)
  let e := vertexIsoOfYonedaHomotopy H
  exact e.map (coherentSmallConstantTargetMap F (coherentDiagramTotalVertex F)) ≪≫
    (coherentTotalUnitRepresentation F).2

end SerrePositivity.InfinityCategories.F2
