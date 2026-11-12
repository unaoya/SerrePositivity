module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertices

/-!
概要：同じ実辺の区間写像族を、終点の等式による表示変更に沿って保持する。
方針：終点の等式と同じ実一単体の等式だけを消去する。
規約：辺を選び直さない。使われ方：元の raw/native 余極限区間族の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実辺と等しい終点から作った区間族は、同じ指定族の表示変更である。 -/
lemma intervalMappingVertexFamily_heq_of_target_eq {X : SSet.{u}}
    {x y y' : X _⦋0⦌} (hy : y = y') (e : X.Edge x y) (e' : X.Edge x y')
    (he : e.edge = e'.edge) :
    HEq (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e))
      (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e')) := by
  cases hy
  have h : e = e' := by
    cases e
    cases e'
    cases he
    rfl
  cases h
  rfl

end SerrePositivity.InfinityCategories.F2
