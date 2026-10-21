module

public import SerrePositivity.InfinityCategories.F2.CoherentTransformationUnitRepresentation

/-!
概要：定値標的への指定表現を保ち、元の合成三角形の長辺を全空間射の表現にする。
方針：元の三角形の大きい合成比較へ指定表現を続け、同じ縮小同型で戻す。
規約：単位に限らず任意の指定表現を使う。使われ方：元の native 単位との合成比較。
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
  (z : SpaceInfinity.{u} _⦋0⦌)
  (a : smallLeftUnstraightening G ⟶ (spaceInfinityObject z).obj)
  (R : CoherentConstantRepresentation G z a)
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G (SSet.const z) t R.1)

/-- 指定表現を第二辺に持つ元の三角形の長辺は、元の全空間射の合成を表す。 -/
def coherentConstantTriangleRepresentation : CoherentConstantRepresentation F z
    (coherentTransformationTotalMap F G t ≫ a) := by
  have e := (unstraighteningTriangleVertexIso F G (SSet.const z) t R.1 T.diagonal
    T.diagram T.first T.second T.long).postcomp
      (constantUnstraighteningFiberProjection _ z ≫ (pointedSpaceFiberValueEquivalence z).hom)
  have er := (CoherentConstantRepresentation.largeIso G z a R).precomp
    (leftUnstraighteningMappingVertexMap F G t).val
  have hlift : (leftUnstraighteningMappingVertexMap F G t).val ≫
      ((smallLeftUnstraighteningIso G).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map a) =
      (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTransformationTotalMap F G t ≫ a) := by
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc,
      coherentTransformationTotalMap_lift]
  have et := functorIsoOfEq (e ≪≫ er) rfl hlift
  have es := VertexIso.map et (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).hom
  rw [smallUnstraighteningHomIso_hom_vertex] at es
  have hl := congrArg (fun v : ((ihom (leftUnstraightening F)).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj)) _⦋0⦌ =>
    (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).hom.app (Opposite.op ⦋0⦌) v)
      (coherentConstantTargetMap_vertex F z T.diagonal)
  rw [← hl] at es
  exact ⟨T.diagonal, es⟩

end SerrePositivity.InfinityCategories.F2
