module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

/-!
概要：関手空間の元の頂点を実射へ戻した後の後合成を、元の頂点の像として計算する。
方針：頂点の全単射の往復と、内部 Hom の後合成の頂点公式を使う。
規約：具体的な大きい射を展開しない。使われ方：全 Kan Hom 輸送の指定点の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の関手頂点を実射に戻して後合成すると、同じ元の頂点の内部 Hom 作用になる。 -/
lemma functorVertexEquiv_symm_post_vertex {A B C : SSet.{u}}
    (x : ((ihom A).obj B) _⦋0⦌) (q : B ⟶ C) :
    ((ihom A).map q).app (Opposite.op ⦋0⦌) x =
      functorVertex ((functorVertexEquiv A B).symm x ≫ q) := by
  have hx := (functorVertexEquiv A B).apply_symm_apply x
  calc
    _ = ((ihom A).map q).app (Opposite.op ⦋0⦌)
        (functorVertex ((functorVertexEquiv A B).symm x)) :=
      congrArg (fun z => ((ihom A).map q).app (Opposite.op ⦋0⦌) z) hx.symm
    _ = _ := rfl

end SerrePositivity.InfinityCategories.F2
