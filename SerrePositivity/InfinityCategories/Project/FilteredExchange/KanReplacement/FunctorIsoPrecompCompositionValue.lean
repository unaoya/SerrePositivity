module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerCancellation

/-!
概要：指定関手同型の二段の前合成を、同じ合成射による前合成へ値を保って移す。
方針：既存の厳密な前合成の合成則を型付き一致として保持する。
規約：指定値を選び直さない。使われ方：単位因子の三角形交換則の明示的な結合則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の二段の前合成と同じ合成射の前合成は、両端の表示も含めて同じ指定値。 -/
lemma functorIso_precomp_precomp_heq {A B X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : B ⟶ X) (q : A ⟶ B) :
    HEq ((e.precomp p).precomp q) (e.precomp (q ≫ p)) :=
  heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e p q)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
