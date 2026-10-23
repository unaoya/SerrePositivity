module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentConstantCoconeComparison

/-!
概要：指定済みの全空間射の表現から、同じ変換を保持する native 余錐を実現する。
方針：元の表現の円柱を join 余錐へ実現し、元の指定比較へ戻す。
規約：表現を選び直さない。使われ方：元の合成三角形の長辺の余錐表示。
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
  (R : CoherentConstantRepresentation F z a)

/-- 概要：指定表現の元の変換の全円柱。
方針：元の辺を uncurry。規約：指定変換を保持。使われ方：元の長辺の実現。 -/
def coherentRepresentationHomotopy : SSet.Homotopy F (SSet.const z) :=
  simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex R.1).toTruncated

/-- 概要：指定表現の元の円柱の全比較付き余錐実現。
方針：両端固定の join 実現。規約：元の円柱を保持。使われ方：余錐の指定値。 -/
def coherentRepresentationCoconeRealization :
    HomotopyCoconeRealization (coherentRepresentationHomotopy F z a R) :=
  homotopyCoconeRealization (coherentRepresentationHomotopy F z a R)

/-- 概要：指定表現の元の変換を表す native 余錐。
方針：比較付き実現を使う。規約：元の図式上の余錐。使われ方：三角形の長辺の表示。 -/
def coherentRepresentationCocone : JoinCocone F :=
  (coherentRepresentationCoconeRealization F z a R).cocone

/-- 概要：指定表現の余錐の頂点は元の指定頂点。
方針：実現の両端固定条件。規約：厳密な等式。使われ方：標準余錐比較。 -/
lemma coherentRepresentationCocone_vertex : (coherentRepresentationCocone F z a R).vertex = z :=
  (coherentRepresentationCoconeRealization F z a R).vertex_eq

/-- 概要：指定表現からの余錐の標準比較は元の全空間射と同型。
方針：同じ変換の実現円柱を写し、元の表現同型を続ける。
規約：指定表現も比較も保持。使われ方：元の三角形と余極限写像との整合。 -/
def coherentRepresentationCoconeComparisonIso :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj))
      ((coherentCoconeTotalComparison F z).app (Opposite.op ⦋0⦌)
        (coconeMappingPointAt (coherentRepresentationCocone F z a R) z
          (coherentRepresentationCocone_vertex F z a R)))
      (ULift.up.{u + 1, u} (functorVertex a)) := by
  let H := coconeRealizationTransformationHomotopy R.1
    (coherentRepresentationCoconeRealization F z a R)
  exact (vertexIsoOfYonedaHomotopy H).map (coherentSmallConstantTargetMap F z) ≪≫ R.2

end SerrePositivity.InfinityCategories.F2
