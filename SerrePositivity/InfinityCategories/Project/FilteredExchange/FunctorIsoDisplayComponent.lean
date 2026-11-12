module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport

/-!
概要：指定関手同型の端点表示変更を、同じ一点成分で除去する。
方針：元の同型の HEq と、成分への同じ評価の可換性を使う。
規約：指定同型を選び直さない。使われ方：元の全作用の curry の固定射成分の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の指定関手同型の端点表示変更は、同じ一点で元の指定成分を保持する。 -/
lemma functorIsoOfEq_app_heq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (x : X _⦋0⦌) : HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).app x) (e.app x) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_app_heq_of_heq _ e hf.symm hg.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq e hf hg) x

end SerrePositivity.InfinityCategories.Project.FilteredExchange
