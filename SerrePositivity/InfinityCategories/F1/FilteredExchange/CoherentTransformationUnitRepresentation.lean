module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingInvertible
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Universe.Kan
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentConstantTargetComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoherentSmallConstantTarget
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantDiagramTransportWitness
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantTargetVertex
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentConstantRepresentationLarge
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalUnitRepresentation
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTransformationTotalMap
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTransformationUnitTriangle
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTransformationVertexTriangle
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.LargeTotalCoconeUnit

/-!
概要：元の変換と指定単位の合成三角形の長辺を小さい全空間射の指定表現にする。
方針：同じ三角形の全空間比較を縮小同型で移し、元の単位を保持する。
規約：元の長辺と全三角形を変更しない。使われ方：元の変換から得る余錐の照合。
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
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)

/-- 概要：元の小さい作用と単位の合成の持ち上げは元の大きい作用と単位の合成。
方針：縮小同型の自然性と持ち上げの関手性。
規約：射の厳密な式。使われ方：指定三角形の比較の終点を揃える。 -/
lemma coherentTransformationTotalMap_unit_lift :
    (leftUnstraighteningMappingVertexMap F G t).val ≫ coherentLargeTotalUnit G =
      (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTransformationTotalMap F G t ≫ coherentDiagramTotalUnit G) := by
  symm
  rw [Functor.map_comp, ← Category.assoc, coherentTransformationTotalMap_lift]
  rfl

/-- 概要：元の合成三角形の指定長辺は元の全空間作用と元の単位の指定表現。
方針：元の大きい全空間比較を縮小の内部 Hom へ移す。
規約：長辺と指定射を保持。使われ方：元の coherent 変換からの余錐の構成。 -/
def coherentTransformationUnitRepresentation
    (T : CoherentTransformationUnitTriangle F G t) :
    CoherentConstantRepresentation F (coherentDiagramTotalVertex G)
      (coherentTransformationTotalMap F G t ≫ coherentDiagramTotalUnit G) := by
  have e := functorIsoOfEq (coherentTransformationUnitTriangleLargeIso F G t T) rfl
    (coherentTransformationTotalMap_unit_lift F G t)
  have es := VertexIso.map e (smallUnstraighteningHomIso F
    (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).hom
  rw [smallUnstraighteningHomIso_hom_vertex] at es
  have hl := congrArg (fun v : ((ihom (leftUnstraightening F)).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (coherentDiagramTotalVertex G)).obj)) _⦋0⦌ =>
    (smallUnstraighteningHomIso F (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).hom.app
      (Opposite.op ⦋0⦌) v)
      (coherentConstantTargetMap_vertex F (coherentDiagramTotalVertex G) T.diagonal)
  rw [← hl] at es
  exact ⟨T.diagonal, es⟩

end SerrePositivity.InfinityCategories.F2
