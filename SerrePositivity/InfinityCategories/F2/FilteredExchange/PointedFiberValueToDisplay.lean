module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedFiberValueTo

/-!
概要：指定頂点等式による元の fiber の値射は、同じ終点表示の標準値射と値まで一致。
方針：頂点の等式を消去する。
規約：元の値射を保持。使われ方：raw/native の同じ対角比較の値への後合成の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定頂点等式の先の元の値射は、同じ終点表示の標準値射と型を含めて一致する。 -/
lemma pointedFiberValueTo_heq_value {z z' : SpaceInfinity.{u} _⦋0⦌} (h : z = z') :
    HEq (pointedFiberValueTo h) (pointedSpaceFiberValueEquivalence z').hom := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.F2
