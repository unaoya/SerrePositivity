module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentConstantTriangleLargeComparison

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
  let et := coherentConstantTriangleLargeComparison F G z a R t T
  have es := VertexIso.map et (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).hom
  rw [smallUnstraighteningHomIso_hom_vertex] at es
  have hl := congrArg (fun v : ((ihom (leftUnstraightening F)).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj)) _⦋0⦌ =>
    (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).hom.app (Opposite.op ⦋0⦌) v)
      (coherentConstantTargetMap_vertex F z T.diagonal)
  rw [← hl] at es
  exact ⟨T.diagonal, es⟩

end SerrePositivity.InfinityCategories.F2
