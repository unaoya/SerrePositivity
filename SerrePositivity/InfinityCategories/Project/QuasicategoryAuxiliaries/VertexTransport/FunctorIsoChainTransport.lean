module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
分割で生成：docstring を書き直すこと
概要：指定同型の三対二の合成式を五つの端点の等式で輸送する。
方針：関手の等式と指定値の型付きの一致を同時に消去する。
規約：新たな同型を選ばない。使われ方：区間錐の自然性の strict な表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：同じ後合成射の二表示は指定同型を型付きで保持。
方針：射の等式を消去。規約：元の値。使われ方：切断成分の同定。 -/
lemma functorIso_postcomp_heq_of_map_eq {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) {r r' : Y ⟶ Z} (h : r = r') :
    HEq (e.postcomp r') (e.postcomp r) := by cases h; rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
