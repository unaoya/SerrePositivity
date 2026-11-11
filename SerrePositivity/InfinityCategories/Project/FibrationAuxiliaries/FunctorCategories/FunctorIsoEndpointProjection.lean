module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：指定関手同型の端点正規化は、後合成が回収する等号の同型を保持する。
方針：端点の等号を消去し、証明の非依存性を使う。
規約：指定された同型と射影を保持する。
使われ方：fiber 内比較と切断の単位比較を同じ端点で照合する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 端点の表示を変更しても、射影後の等号同型は同じ端点の等号同型となる。 -/
lemma functorIsoOfEq_postcomp_eqToIso {A E B : SSet.{u}}
    {f g f' g' : A ⟶ E} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : E ⟶ B) (h : f ≫ p = g ≫ p) (h' : f' ≫ p = g' ≫ p)
    (he : e.postcomp p = eqToIso (congrArg
      (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) h)) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).postcomp p = eqToIso (congrArg
      (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) h') := by
  subst f' g'
  exact he

/-- 端点だけの正規化後に前合成しても、指定された元の同型の値を保持する。 -/
lemma functorIsoOfEq_precomp_heq {A E K : SSet.{u}}
    {f g f' g' : A ⟶ E} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (r : K ⟶ A) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).precomp r) (e.precomp r) := by
  subst f' g'
  rfl

/-- 端点だけの正規化後に後合成しても、指定された元の同型の値を保持する。 -/
lemma functorIsoOfEq_postcomp_heq {A E B : SSet.{u}}
    {f g f' g' : A ⟶ E} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : E ⟶ B) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).postcomp p) (e.postcomp p) := by
  subst f' g'
  rfl

/-- 端点正規化された同じ指定値との等式は、後合成後もその元の値を保持する。 -/
lemma functorIsoOfEq_postcomp_heq_of_eq {A E B : SSet.{u}}
    {f g f' g' : A ⟶ E} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg = e') (p : E ⟶ B) :
    HEq (e'.postcomp p) (e.postcomp p) := by
  subst e'
  exact functorIsoOfEq_postcomp_heq e hf hg p

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
