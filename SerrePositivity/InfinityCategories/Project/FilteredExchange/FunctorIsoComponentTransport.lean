module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：指定関手同型の等式移送は実際の各点成分の HEq を保つ。
方針：両端の関手の等式と指定同型の HEq を順に除去する。
規約：指定同型を再選択しない。使われ方：unstraightening 比較の正規化の除去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 指定関手同型の正規化前後で、各点の実際の成分は HEq で一致する。 -/
lemma functorIso_app_heq_of_heq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (x : X _⦋0⦌) :
    HEq (e.app x) (e'.app x) := by
  cases hf
  cases hg
  cases he
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
