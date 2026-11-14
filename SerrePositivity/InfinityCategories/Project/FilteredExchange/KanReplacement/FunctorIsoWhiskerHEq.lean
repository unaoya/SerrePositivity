module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：明示した端点等式の下で、指定同型の逆と二段の後合成の型付き一致を保つ。
方針：元の二射の等式と指定同型の一致を同時に消去する。
規約：HEq から端点等式を抽出しない。使われ方：共通の引き戻し比較の底の像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 明示した両端と指定値の一致は、同じ逆同型の指定値も保持する。 -/
lemma functorIso_symm_heq_of_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f = f') (hg : g = g')
    (h : HEq e' e) : HEq e'.symm e.symm := by
  subst f' g'
  cases eq_of_heq h
  rfl

/-- 明示した両端と指定値の一致は、同じ二つの射の後合成でも保持される。 -/
lemma functorIso_postcomp_postcomp_heq_of_heq {X Y Z W : SSet.{u}}
    {f g f' g' : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (hf : f = f') (hg : g = g') (h : HEq e' e) (p : Y ⟶ Z) (q : Z ⟶ W) :
    HEq ((e'.postcomp p).postcomp q) ((e.postcomp p).postcomp q) := by
  subst f' g'
  cases eq_of_heq h
  rfl

/-- 元の端点補正を二段の後合成の前に入れても指定値を保つ。 -/
lemma functorIsoOfEq_postcomp_twice_heq {A X Y Z : SSet.{u}}
    {f g f' g' : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : X ⟶ Y) (q : Y ⟶ Z) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).postcomp p).postcomp q)
      ((e.postcomp p).postcomp q) := by
  subst f' g'
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
