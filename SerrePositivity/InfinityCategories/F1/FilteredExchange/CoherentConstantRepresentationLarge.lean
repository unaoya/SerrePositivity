module

public import SerrePositivity.InfinityCategories.Core.Equivalence
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
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalUnitRepresentation
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.LargeTotalCoconeUnit

/-!
概要：指定全空間射の coherent な表現を大きい全空間上の実際の射として比較する。
方針：内部 Hom の縮小同型を戻し、定値標的の fiber 座標で評価する。
規約：元の変換と指定射を保持。使われ方：元の単位を合成三角形で使う。
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

/-- 概要：小さい定値標的比較を戻すと元の大きい定値標的比較。
方針：縮小同型の往復を消去。規約：頂点の厳密な等式。使われ方：指定表現の移送。 -/
lemma coherentSmallConstantTargetMap_inv_vertex (z : SpaceInfinity.{u} _⦋0⦌)
    (t : (leftUnstraighteningTransformationSpace F (SSet.const z)) _⦋0⦌) :
    (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv.app (Opposite.op ⦋0⦌)
      ((coherentSmallConstantTargetMap F z).app (Opposite.op ⦋0⦌) t) =
        (coherentConstantTargetMap F z).app (Opposite.op ⦋0⦌) t := by
  have h : coherentSmallConstantTargetMap F z ≫
      (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv =
        coherentConstantTargetMap F z := by
    simp only [coherentSmallConstantTargetMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun q => q.app (Opposite.op ⦋0⦌) t) h

/-- 概要：大きい全空間上の指定射を縮小の内部 Hom で送ると元の小さい射の頂点。
方針：既存の逆方向の頂点式と同型の往復。
規約：元の射を保持。使われ方：三角形の比較を小さい全空間へ戻す。 -/
lemma smallUnstraighteningHomIso_hom_vertex {Z : SSet.{u}}
    (a : smallLeftUnstraightening F ⟶ Z) :
    (smallUnstraighteningHomIso F Z).hom.app (Opposite.op ⦋0⦌)
      (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map a)) = ULift.up.{u + 1, u} (functorVertex a) := by
  rw [← smallUnstraighteningHomIso_inv_vertex]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (smallUnstraighteningHomIso F Z).inv_hom_id (Opposite.op ⦋0⦌)) _

/-- 概要：元の表現の変換の実際の全空間作用は元の指定射の持ち上げと同型。
方針：表現同型を内部 Hom の縮小の逆へ写し、元の fiber の座標へ移す。
規約：元の表現データを保持。使われ方：元の単位の合成への入力。 -/
def CoherentConstantRepresentation.largeIso (z : SpaceInfinity.{u} _⦋0⦌)
    (a : smallLeftUnstraightening F ⟶ (spaceInfinityObject z).obj)
    (R : CoherentConstantRepresentation F z a) :
    FunctorIso ((leftUnstraighteningMappingVertexMap F (SSet.const z) R.1).val ≫
      constantUnstraighteningFiberProjection _ z ≫ (pointedSpaceFiberValueEquivalence z).hom)
      ((smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map a) := by
  have e := R.2.map (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv
  rw [coherentSmallConstantTargetMap_inv_vertex, coherentConstantTargetMap_vertex,
    smallUnstraighteningHomIso_inv_vertex] at e
  exact e

end SerrePositivity.InfinityCategories.F2
