module

public import SerrePositivity.InfinityCategories.F2.CoherentConstantTriangleRepresentationValue
public import SerrePositivity.InfinityCategories.F2.VertexIsoIsoRoundtrip

/-!
概要：三角形から作った指定表現を大きい表示へ戻し、元の比較を値まで回収する。
方針：元の指定値を縮小同型と逆で写す往復へ揃え、その往復を消去する。
規約：単位や三角形を選び直さない。使われ方：既存の上面の作用比較との接続。
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

/-- 三角形表現の縮小と復元は、同じ三角形・同じ第二辺の元の大きい比較に戻る。 -/
lemma coherentConstantTriangleRepresentation_largeIso_eq :
    CoherentConstantRepresentation.largeIso F z
      (coherentTransformationTotalMap F G t ≫ a)
      (coherentConstantTriangleRepresentation F G z a R t T) =
        coherentConstantTriangleLargeComparison F G z a R t T := by
  let i := smallUnstraighteningHomIso F (spaceInfinityObject z).obj
  let e := coherentConstantTriangleLargeComparison F G z a R t T
  let r := coherentConstantTriangleRepresentation F G z a R t T
  have hs : (coherentSmallConstantTargetMap F z).app (Opposite.op ⦋0⦌) r.1 =
      i.hom.app (Opposite.op ⦋0⦌)
        (functorVertex ((leftUnstraighteningMappingVertexMap F (SSet.const z) T.diagonal).val ≫
          constantUnstraighteningFiberProjection _ z ≫
            (pointedSpaceFiberValueEquivalence z).hom)) := by
    change i.hom.app _ ((coherentConstantTargetMap F z).app _ T.diagonal) = _
    exact congrArg (fun v => i.hom.app (Opposite.op ⦋0⦌) v)
      (coherentConstantTargetMap_vertex F z T.diagonal)
  have ht : ULift.up.{u + 1, u} (functorVertex (coherentTransformationTotalMap F G t ≫ a)) =
      i.hom.app (Opposite.op ⦋0⦌)
        (functorVertex ((smallLeftUnstraighteningIso F).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map (coherentTransformationTotalMap F G t ≫ a))) :=
    (smallUnstraighteningHomIso_hom_vertex F (coherentTransformationTotalMap F G t ≫ a)).symm
  have h := vertexIso_map_heq_of_heq r.2 (VertexIso.map e i.hom) hs ht
    (coherentConstantTriangleRepresentation_value_heq F G z a R t T) i.inv
  exact eq_of_heq ((CoherentConstantRepresentation.largeIso_heq_map F z
    (coherentTransformationTotalMap F G t ≫ a) r).trans
      (h.trans (vertexIso_map_iso_roundtrip i e)))

end SerrePositivity.InfinityCategories.F2
