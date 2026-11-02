module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberValueMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeRealizationTransformation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentSmallConstantTarget
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.HomotopyCoconeRealization
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.YonedaHomotopyVertex
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentConstantCocone
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.LargeTotalCoconeUnit
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingSpace

/-!
概要：指定射から実現した native 余錐の標準比較を元の指定射と照合する。
方針：両端固定の円柱を変換空間へ戻し、指定射の表現同型と合成する。
規約：元の図式・頂点・指定射を保持。使われ方：全空間射影から余極限写像への接続。
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
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (z : SpaceInfinity.{u} _⦋0⦌)
  (a : smallLeftUnstraightening F ⟶ (spaceInfinityObject z).obj)

/-- 概要：元の余錐の標準比較の像は指定した全空間の射と同型。
方針：実現の比較円柱を写して表現同型に続ける。
規約：両端の指定値を保持。使われ方：余錐比較の像の照合。 -/
def coherentConstantCoconeComparisonIso :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj))
      ((coherentCoconeTotalComparison F z).app (Opposite.op ⦋0⦌)
        (coconeMappingPointAt (coherentConstantCocone F z a) z
          (coherentConstantCocone_vertex F z a)))
      (ULift.up.{u + 1, u} (functorVertex a)) := by
  let H := coconeRealizationTransformationHomotopy
    (coherentConstantRepresentation F z a).1 (coherentConstantCoconeRealization F z a)
  let e := vertexIsoOfYonedaHomotopy H
  exact e.map (coherentSmallConstantTargetMap F z) ≪≫
    (coherentConstantRepresentation F z a).2

/-- 概要：元の余錐の fiber 評価は元の指定射の持ち上げと関手同型。
方針：内部 Hom の縮小同型を戻し、同じ指定射の比較を移す。
規約：大きい全空間からの実際の射。使われ方：全 Hom の前合成との照合。 -/
def coherentConstantCoconeFiberIso :
    FunctorIso (coconeFiberValueMapAt (coherentConstantCocone F z a) z
      (coherentConstantCocone_vertex F z a))
      ((smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map a) := by
  have e := (coherentConstantCoconeComparisonIso F z a).map
    (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv
  rw [coconeFiberValueMapAt_smallComparison, smallUnstraighteningHomIso_inv_vertex] at e
  exact e

end SerrePositivity.InfinityCategories.F2
