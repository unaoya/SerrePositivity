module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：元の指定関手同型の curry を、同じ指定値の関手空間上の像へ戻す。
方針：curry の両端の頂点表示による移送だけを除く。
規約：指定比較を保持。使われ方：全族の比較の各点評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の指定同型の curry は、同じ指定同型の関手空間上の curry の像。 -/
lemma functorIso_curry_heq_map {A B X : SSet.{u}} [Quasicategory X]
    {f g : A ⊗ B ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    HEq e.curry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry
  have hcast {α β : Sort (u + 1)} (h : α = β) (z : α) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
