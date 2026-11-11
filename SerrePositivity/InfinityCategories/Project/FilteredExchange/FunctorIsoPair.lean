module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：同じパラメータの第二成分を固定した直積への関手同型を構成する。
方針：評価と第二成分を組にした関手空間の射で、元の指定同型を写す。
規約：新しい辺を選ばない。使われ方：区間輸送の始点の指定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 関手空間の元を、同じパラメータで動く指定第二成分と組にする射。 -/
def functorPairRight {P A B : SSet.{u}} (y : P ⟶ B) :
    (ihom P).obj A ⟶ (ihom P).obj (A ⊗ B) :=
  curry (lift (uncurry (𝟙 ((ihom P).obj A))) (fst P ((ihom P).obj A) ≫ y))

/-- 元の関手の頂点を写すと、指定第二成分との組の頂点そのもの。 -/
lemma functorPairRight_vertex {P A B : SSet.{u}} (f : P ⟶ A) (y : P ⟶ B) :
    (functorPairRight y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift f y) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro p
  rfl

/-- 同じ第二成分を保つ直積への指定関手同型。 -/
def functorIsoLiftRight {P A B : SSet.{u}} {f g : P ⟶ A}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (y : P ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (lift f y) (lift g y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (functorPairRight y)
  rw [functorPairRight_vertex, functorPairRight_vertex] at h
  exact h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
