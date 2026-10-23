module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorInvertibleDetection

/-!
概要：始域の全頂点を覆う族に沿って、元の指定辺を保つ Hom の可逆性を降下させる。
方針：局所的な成分を評価し、制限と評価の厳密な可換性で全体の成分へ戻す。
規約：指定辺の保存と、可逆性を検査する頂点の被覆を区別する。
使われ方：指定辺を保つ Hom の族を core の族へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全頂点を覆う族の各制限で可逆なら、元の指定辺を保つ Hom の辺は可逆。 -/
lemma isInvertibleEdge_markedCocartesianFunctor_of_vertex_cover
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
    {J : Type v} (a : Over B) (D : J → Over B) (i : ∀ j, D j ⟶ a)
    (U : Set (a.left _⦋1⦌)) (W : ∀ j, Set ((D j).left _⦋1⦌))
    (hi : ∀ j e, e ∈ W j → (i j).left.app (Opposite.op ⦋1⦌) e ∈ U)
    (hc : ∀ x : a.left _⦋0⦌, ∃ j y, (i j).left.app (Opposite.op ⦋0⦌) y = x)
    {v w : (markedCocartesianFunctorSpace q a.hom U) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (markedCocartesianFunctorSpace q a.hom U)) v w)
    (he : ∀ j, IsInvertibleEdge (X := markedCocartesianFunctorSpace q (D j).hom (W j))
      (e.map ((truncation 2).map (markedCocartesianFunctorPre q (i j) (W j) U (hi j))))) :
    IsInvertibleEdge e := by
  apply (isInvertibleEdge_markedCocartesianFunctor_iff_evaluate q a.hom U e).mpr
  intro x
  obtain ⟨j, y, rfl⟩ := hc x
  have h := (he j).map (markedCocartesianFunctorEvaluate q (D j).hom (W j) y)
  apply (isInvertibleEdge_congr
    (e := (e.map ((truncation 2).map (markedCocartesianFunctorPre q (i j) (W j) U (hi j)))).map
      ((truncation 2).map (markedCocartesianFunctorEvaluate q (D j).hom (W j) y)))
    (f := e.map ((truncation 2).map
      (markedCocartesianFunctorEvaluate q a.hom U
        ((i j).left.app (Opposite.op ⦋0⦌) y)))) ?_).mp h
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e.edge)
    (markedCocartesianFunctorEvaluate_overPre q (i j) (W j) U (hi j) y)

end SerrePositivity.InfinityCategories
