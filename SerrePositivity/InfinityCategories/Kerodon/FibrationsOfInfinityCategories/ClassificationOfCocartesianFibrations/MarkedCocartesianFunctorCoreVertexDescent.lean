module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorInvertibleDetection

/-!
概要：始域の全頂点を覆う族に沿って、元の指定辺を保つ Hom の可逆性を降下させる。
方針：局所的な成分を評価し、制限と評価の厳密な可換性で全体の成分へ戻す。
規約：指定辺の保存と、可逆性を検査する頂点の被覆を区別する。
使われ方：指定辺を保つ Hom の族を core の族へ戻す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 全頂点を覆う族の各制限で可逆なら、元の指定辺を保つ Hom の辺は可逆。 -/
lemma isInvertibleEdge_markedCocartesianFunctor_of_vertex_cover
    {E B : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
    {J : Type v} (a : Over B) (D : J → Over B) (i : ∀ j, D j ⟶ a)
    (U : Set (a.left _⦋1⦌)) (W : ∀ j, Set ((D j).left _⦋1⦌))
    (hi : ∀ j e, e ∈ W j → (i j).left.app (Opposite.op ⦋1⦌) e ∈ U)
    (hc : ∀ x : a.left _⦋0⦌, ∃ j y, (i j).left.app (Opposite.op ⦋0⦌) y = x)
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q a.hom U) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q a.hom U)) v w)
    (he : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorSpace q (D j).hom (W j))
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (i j) (W j) U (hi j))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isInvertibleEdge_markedCocartesianFunctor_iff_evaluate q a.hom U e).mpr
  intro x
  obtain ⟨j, y, rfl⟩ := hc x
  have h := (he j).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorEvaluate q (D j).hom (W j) y)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorPre q (i j) (W j) U (hi j)))).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorEvaluate q (D j).hom (W j) y)))
    (f := e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorEvaluate q a.hom U
        ((i j).left.app (Opposite.op ⦋0⦌) y)))) ?_).mp h
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e.edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorEvaluate_overPre q (i j) (W j) U (hi j) y)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
