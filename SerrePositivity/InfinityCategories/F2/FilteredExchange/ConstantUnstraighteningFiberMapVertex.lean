module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantUnstraighteningValueVertex

/-!
概要：定値相対 Hom の任意の fiber 射への作用を、元の実相対射の頂点で計算する。
方針：元の fiber 射影の実頂点式に同じ指定射を続ける。
規約：元の実射と指定射影を保持。使われ方：定値三角形の固定値への実端点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対実射の任意の fiber 値への像は、同じ実射・fiber 射影・値射の合成の頂点。 -/
lemma constantUnstraighteningRelativeIso_fiberMap_vertex {A B X : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (f : A ⟶ leftUnstraightening (SSet.const z : B ⟶ SpaceInfinity))
    (hf : f ≫ leftUnstraighteningProjection (SSet.const z) = a)
    (g : vertexFiber pointedSpaceProjection z ⟶ X) :
    ((constantUnstraighteningRelativeIso a z).hom ≫ (ihom A).map g).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z)) a f hf) =
        functorVertex (f ≫ constantUnstraighteningFiberProjection B z ≫ g) := by
  change ((ihom A).map g).app _ ((constantUnstraighteningRelativeIso a z).hom.app _ _) = _
  rw [constantUnstraighteningRelativeIso_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2
