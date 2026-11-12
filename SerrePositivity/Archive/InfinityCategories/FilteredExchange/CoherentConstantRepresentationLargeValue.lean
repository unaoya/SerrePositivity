module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentConstantRepresentationLarge
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：指定表現を大きい全空間へ戻す操作の、元の比較の値を明示する。
方針：端点表示の等式輸送を除き、縮小同型の逆による像を保持する。
規約：指定比較を選び直さない。使われ方：単位上面の指定比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 大きい表示へ戻す指定比較は、元の表現の比較を縮小同型の逆で写した同じ値。 -/
lemma CoherentConstantRepresentation.largeIso_heq_map {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌)
    (a : smallLeftUnstraightening F ⟶ (spaceInfinityObject z).obj)
    (R : CoherentConstantRepresentation F z a) :
    HEq (CoherentConstantRepresentation.largeIso F z a R)
      (VertexIso.map R.2 (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv) := by
  unfold CoherentConstantRepresentation.largeIso
  have hcast {α β : Sort _} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  exact (hcast _ _).trans ((hcast _ _).trans (hcast _ _))

end SerrePositivity.InfinityCategories.F2
