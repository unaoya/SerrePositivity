module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentConstantTriangleRepresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentConstantRepresentationLargeValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalComponent
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の三角形で作った指定表現の比較の値を、元の大きい比較へ戻す。
方針：端点表示の等式輸送を外し、同じ縮小同型による像を保持する。
規約：指定表現を選び直さない。使われ方：上面の native 作用比較の値の同定。
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

/-- 三角形表現の小さい比較は、元の大きい比較を縮小同型で写した同じ指定値。 -/
lemma coherentConstantTriangleRepresentation_value_heq :
    HEq (coherentConstantTriangleRepresentation F G z a R t T).2
      (VertexIso.map (coherentConstantTriangleLargeComparison F G z a R t T)
        (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).hom) := by
  unfold coherentConstantTriangleRepresentation
  dsimp only
  have hcast {α β : Sort _} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  exact (hcast _ _).trans (hcast _ _)

end SerrePositivity.InfinityCategories.F2
