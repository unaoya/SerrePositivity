module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoChainTransport
/-!
概要：指定された全関手同型の可換四角形を、同じ端点と異種等式で輸送する。
方針：端点の等式と同型の指定値を同時に消去する。
規約：新しい比較を選ばない。使われ方：元の raw factor と制限比較の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 全端点の等式と同じ指定値を保って、全関手同型の四角形の等式を反映する。 -/
lemma functorIso_two_two_transport {X Y : SSet.{u}}
    {f g h k f' g' h' k' : X ⟶ Y}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g k) (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f h) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso h k)
    (c' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (r' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' k')
    (q' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' h') (d' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso h' k')
    (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (hc : HEq c c') (hr : HEq r r') (hq : HEq q q') (hd : HEq d d')
    (he : c' ≪≫ r' = q' ≪≫ d') : c ≪≫ r = q ≪≫ d := by
  subst f' g' h' k'
  cases eq_of_heq hc
  cases eq_of_heq hr
  cases eq_of_heq hq
  cases eq_of_heq hd
  exact he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
