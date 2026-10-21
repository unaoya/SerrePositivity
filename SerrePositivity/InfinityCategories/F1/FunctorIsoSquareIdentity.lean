module

public import SerrePositivity.InfinityCategories.F1.FunctorIsoPastingTransport

/-!
概要：四端点と四つの指定関手同型を保つ、輸送三角形の貼り合わせ等式。
方針：端点の等式を消去して同じ指定値の合成を回収する。
規約：元の同型の値を保持する。
使われ方：元の全 Hom 上の三角形を局所自然性と同じ端点へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 指定された二つの二辺の貼り合わせは同じ値。 -/
def FunctorIsoSquareCommutes {X Y : SSet.{u}} {a b c t : X ⟶ Y}
    (e : FunctorIso a b) (d : FunctorIso b t)
    (v : FunctorIso a c) (f : FunctorIso c t) : Prop := e ≪≫ d = v ≪≫ f

/-- 同じ四端点への正規化は、四つの指定値とその貼り合わせ等式を保持する。 -/
lemma functorIsoSquareCommutes_reindex {X Y : SSet.{u}}
    {a b c t a' b' c' t' : X ⟶ Y}
    (ha : a = a') (hb : b = b') (hc : c = c') (ht : t = t')
    (e : FunctorIso a b) (d : FunctorIso b t)
    (v : FunctorIso a c) (f : FunctorIso c t)
    (e' : FunctorIso a' b') (d' : FunctorIso b' t')
    (v' : FunctorIso a' c') (f' : FunctorIso c' t')
    (h : FunctorIsoSquareCommutes e d v f)
    (he : HEq e' e) (hd : HEq d' d) (hv : HEq v' v) (hf : HEq f' f) :
    FunctorIsoSquareCommutes e' d' v' f' := by
  subst a' b' c' t'
  cases eq_of_heq he
  cases eq_of_heq hd
  cases eq_of_heq hv
  cases eq_of_heq hf
  exact h

/-- 指定同型が持つ始点の作用。 -/
def FunctorIso.sourceMap {X Y : SSet.{u}} {f g : X ⟶ Y} (_e : FunctorIso f g) :
    X ⟶ Y := f

/-- 指定同型が持つ終点の作用。 -/
def FunctorIso.targetMap {X Y : SSet.{u}} {f g : X ⟶ Y} (_e : FunctorIso f g) :
    X ⟶ Y := g

end SerrePositivity.InfinityCategories
