module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection

/-!
概要：指定関手同型の貼り合わせを、同じ三端点の表示変更で移す。
方針：端点の等式を消去し、同じ指定同型の型付きの一致を使う。
規約：新たな同型や辺の代表を選ばない。
使われ方：元の第二辺の二因子を既存の自然性同型の合成に同定する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 三端点を同じ表示に移した二つの指定同型の合成は、元の合成の値を保持する。 -/
lemma functorIso_trans_heq_of_heq {A X : SSet.{u}} {f g h f' g' h' : A ⟶ X}
    (hf : f = f') (hg : g = g') (hh : h = h')
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h)
    (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (d' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' h')
    (he : HEq e' e) (hd : HEq d' d) : HEq (e' ≪≫ d') (e ≪≫ d) := by
  subst f' g' h'
  cases eq_of_heq he
  cases eq_of_heq hd
  rfl

/-- 同じ前後合成と三端点の正規化を保って、元の指定二因子を貼り合わせる。 -/
lemma functorIso_postcomp_precomp_trans_heq {H X Y K : SSet.{u}}
    {f g : H ⟶ X} {h : H ⟶ Y} (p : X ⟶ Y) (r : K ⟶ H)
    {f' g' : K ⟶ X} {h' : K ⟶ Y}
    (hf : r ≫ f = f') (hg : r ≫ g = g') (hh : r ≫ h = h')
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ p) h)
    (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (d' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g' ≫ p) h')
    (he : HEq (e'.postcomp p) ((e.postcomp p).precomp r))
    (hd : HEq d' (d.precomp r)) :
    HEq (e'.postcomp p ≪≫ d') ((e.postcomp p).precomp r ≪≫ d.precomp r) := by
  exact functorIso_trans_heq_of_heq
    ((Category.assoc r f p).symm.trans (congrArg (fun v ↦ v ≫ p) hf))
    ((Category.assoc r g p).symm.trans (congrArg (fun v ↦ v ≫ p) hg)) hh
    _ _ _ _ he hd

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
