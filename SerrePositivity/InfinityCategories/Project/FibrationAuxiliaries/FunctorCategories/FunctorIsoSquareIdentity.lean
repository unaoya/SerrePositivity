module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPastingTransport

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
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 指定された二つの二辺の貼り合わせは同じ値。 -/
def FunctorIsoSquareCommutes {X Y : SSet.{u}} {a b c t : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b t)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a c) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c t) : Prop := e ≪≫ d = v ≪≫ f

/-- 同じ四端点への正規化は、四つの指定値とその貼り合わせ等式を保持する。 -/
lemma functorIsoSquareCommutes_reindex {X Y : SSet.{u}}
    {a b c t a' b' c' t' : X ⟶ Y}
    (ha : a = a') (hb : b = b') (hc : c = c') (ht : t = t')
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b t)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a c) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c t)
    (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' b') (d' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b' t')
    (v' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' c') (f' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c' t')
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
def FunctorIso.sourceMap {X Y : SSet.{u}} {f g : X ⟶ Y} (_e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    X ⟶ Y := f

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (sourceMap)


/-- 指定同型が持つ終点の作用。 -/
def FunctorIso.targetMap {X Y : SSet.{u}} {f g : X ⟶ Y} (_e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    X ⟶ Y := g

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (targetMap)


/-- 同じ前合成作用の二分解は、指定同型の両端も同じ射として回収する。 -/
lemma FunctorIso.precomp_square_endpoints {H₀ H₁ X Y K : SSet.{u}}
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (p₀ : H₀ ⟶ X) (r₀ : K ⟶ H₀) (p₁ : H₁ ⟶ X) (r₁ : K ⟶ H₁)
    (h : r₀ ≫ p₀ = r₁ ≫ p₁) :
    ((e.precomp p₀).precomp r₀).sourceMap =
      ((e.precomp p₁).precomp r₁).sourceMap ∧
    ((e.precomp p₀).precomp r₀).targetMap =
      ((e.precomp p₁).precomp r₁).targetMap := by
  constructor
  · simpa only [sourceMap, Category.assoc] using congrArg (fun m ↦ m ≫ f) h
  · simpa only [targetMap, Category.assoc] using congrArg (fun m ↦ m ≫ g) h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (precomp_square_endpoints)


/-- 端点正規化後の始点は、元の始点を回収する同じ射から回収される。 -/
lemma functorIsoOfEq_sourceMap_of_eq {X Y : SSet.{u}} {f g f' g' a : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') (h : a = f) :
    a = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).sourceMap := h.trans hf

/-- 端点正規化後の終点は、元の終点を回収する同じ射から回収される。 -/
lemma functorIsoOfEq_targetMap_of_eq {X Y : SSet.{u}} {f g f' g' a : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') (h : a = g) :
    a = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).targetMap := h.trans hg

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
