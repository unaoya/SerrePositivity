module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の指定比較の実端点の表示変更を、任意の前合成後も保持する。
方針：実射の二等式を変数のまま消去する。
規約：比較を選び直さない。使われ方：raw 輸送模型比較の単位での指定像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 元の実端点での表示変更は、任意の実前合成後も同じ指定値を保持する。 -/
lemma functorIsoOfEq_precomp_heq {A X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') (p : A ⟶ X) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).precomp p) (e.precomp p) := by
  subst f' g'
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
