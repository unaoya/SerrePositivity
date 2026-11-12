module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoAlgebra

/-!
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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：五端点の等式と同型の指定値を保持して合成式を輸送する。
方針：端点と同型の等式を消去。規約：指定値。使われ方：strict な自然性の回収。 -/
lemma functorIso_chain_transport {X Y : SSet.{u}}
    {a b c d e a' b' c' d' e' : X ⟶ Y}
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (m : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b c) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c d)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a e) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e d)
    (l' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' b') (m' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b' c') (r' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c' d')
    (s' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' e') (t' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e' d')
    (h : l ≪≫ m ≪≫ r = s ≪≫ t)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e')
    (hl : HEq l' l) (hm : HEq m' m) (hr : HEq r' r)
    (hs : HEq s' s) (ht : HEq t' t) : l' ≪≫ m' ≪≫ r' = s' ≪≫ t' := by
  subst a' b' c' d' e'
  cases eq_of_heq hl
  cases eq_of_heq hm
  cases eq_of_heq hr
  cases eq_of_heq hs
  cases eq_of_heq ht
  exact h

/-- 概要：等式から来る同型を端点の等式で移すと指定された標準同型に一致。
方針：端点を消去し proof irrelevance を使う。
規約：元の指定値。使われ方：strict な図式面・錐面の同定。 -/
lemma functorEqIso_heq_of_isFunctorEqIso {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso e)
    (hf : f = f') (hg : g = g') (h : f' = g') : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso h) e := by
  subst f' g'
  exact heq_of_eq (he.eq h).symm

/-- 概要：中央の標準同型と終域の等式を消して両経路の指定値を比較する。
方針：二端点の等式を消去。規約：元の値。使われ方：錐の中心脚の正規化。 -/
lemma functorIso_transport_image_square {X Y : SSet.{u}} {f g g' h h' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' h') (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f h)
    (hs : g' = g) (ht : h = h')
    (ha : a ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso hs.symm ≪≫ e = r ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso ht) :
    a ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hs rfl = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq r rfl ht := by
  subst g' h'
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq, Iso.trans_refl, Iso.refl_trans] using ha

/-- 概要：終域をさらに等式で移した二経路の指定比較を保つ。
方針：三端点の等式を消去。規約：元の値。使われ方：右枝から左中心への表示変更。 -/
lemma functorIso_transport_image_square_target {X Y : SSet.{u}}
    {f g g' h h' h'' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' h') (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f h)
    (hs : g' = g) (ht : h = h') (hu : h' = h'')
    (ha : a ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso hs.symm ≪≫ e = r ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso ht) :
    a ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hs hu = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq r rfl (ht.trans hu) := by
  subst g' h' h''
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq, Iso.trans_refl, Iso.refl_trans] using ha

end SerrePositivity.InfinityCategories.Project.FilteredExchange
