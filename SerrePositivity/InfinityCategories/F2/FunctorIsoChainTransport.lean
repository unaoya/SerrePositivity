module

public import SerrePositivity.InfinityCategories.F2.FunctorIsoTransportAlgebra

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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：五端点の等式と同型の指定値を保持して合成式を輸送する。
方針：端点と同型の等式を消去。規約：指定値。使われ方：strict な自然性の回収。 -/
lemma functorIso_chain_transport {X Y : SSet.{u}}
    {a b c d e a' b' c' d' e' : X ⟶ Y}
    (l : FunctorIso a b) (m : FunctorIso b c) (r : FunctorIso c d)
    (s : FunctorIso a e) (t : FunctorIso e d)
    (l' : FunctorIso a' b') (m' : FunctorIso b' c') (r' : FunctorIso c' d')
    (s' : FunctorIso a' e') (t' : FunctorIso e' d')
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

/-- 概要：同じ後合成射の二表示は指定同型を型付きで保持。
方針：射の等式を消去。規約：元の値。使われ方：切断成分の同定。 -/
lemma functorIso_postcomp_heq_of_map_eq {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) {r r' : Y ⟶ Z} (h : r = r') :
    HEq (e.postcomp r') (e.postcomp r) := by cases h; rfl

/-- 概要：等式から来る同型を端点の等式で移すと指定された標準同型に一致。
方針：端点を消去し proof irrelevance を使う。
規約：元の指定値。使われ方：strict な図式面・錐面の同定。 -/
lemma functorEqIso_heq_of_isFunctorEqIso {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (he : IsFunctorEqIso e)
    (hf : f = f') (hg : g = g') (h : f' = g') : HEq (functorEqIso h) e := by
  subst f' g'
  exact heq_of_eq (he.eq h).symm

/-- 概要：中央の標準同型と終域の等式を消して両経路の指定値を比較する。
方針：二端点の等式を消去。規約：元の値。使われ方：錐の中心脚の正規化。 -/
lemma functorIso_transport_image_square {X Y : SSet.{u}} {f g g' h h' : X ⟶ Y}
    (a : FunctorIso f g) (e : FunctorIso g' h') (r : FunctorIso f h)
    (hs : g' = g) (ht : h = h')
    (ha : a ≪≫ functorEqIso hs.symm ≪≫ e = r ≪≫ functorEqIso ht) :
    a ≪≫ functorIsoOfEq e hs rfl = functorIsoOfEq r rfl ht := by
  subst g' h'
  simpa only [functorEqIso, functorIsoOfEq, Iso.trans_refl, Iso.refl_trans] using ha

/-- 概要：終域をさらに等式で移した二経路の指定比較を保つ。
方針：三端点の等式を消去。規約：元の値。使われ方：右枝から左中心への表示変更。 -/
lemma functorIso_transport_image_square_target {X Y : SSet.{u}}
    {f g g' h h' h'' : X ⟶ Y}
    (a : FunctorIso f g) (e : FunctorIso g' h') (r : FunctorIso f h)
    (hs : g' = g) (ht : h = h') (hu : h' = h'')
    (ha : a ≪≫ functorEqIso hs.symm ≪≫ e = r ≪≫ functorEqIso ht) :
    a ≪≫ functorIsoOfEq e hs hu = functorIsoOfEq r rfl (ht.trans hu) := by
  subst g' h' h''
  simpa only [functorEqIso, functorIsoOfEq, Iso.trans_refl, Iso.refl_trans] using ha

end SerrePositivity.InfinityCategories.F2
