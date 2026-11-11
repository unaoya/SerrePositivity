module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareIdentity
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPrecompositionProjection

/-!
概要：端点正規化した指定同型を前合成しても、同じ両端と指定値を回収する。
方針：一般の射の等式で正規化を扱い、具体的な同型を展開しない。
規約：元の同型と元の前合成作用を保持する。
使われ方：既存の局所自然性を元の全 Hom へ戻した同じ指定合成の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 前合成した始点の回収は、元の端点正規化後も同じ射を回収する。 -/
lemma functorIsoOfEq_precomp_sourceMap_of_eq {X Y K : SSet.{u}}
    {f g f' g' : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (r : K ⟶ X) {a : K ⟶ Y} (h : (e.precomp r).sourceMap = a) :
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).precomp r).sourceMap = a := by
  change r ≫ f = a at h
  exact (congrArg (fun m ↦ r ≫ m) hf.symm).trans h

/-- 前合成した終点の回収は、元の端点正規化後も同じ射を回収する。 -/
lemma functorIsoOfEq_precomp_targetMap_of_eq {X Y K : SSet.{u}}
    {f g f' g' : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (r : K ⟶ X) {a : K ⟶ Y} (h : (e.precomp r).targetMap = a) :
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).precomp r).targetMap = a := by
  change r ≫ g = a at h
  exact (congrArg (fun m ↦ r ≫ m) hg.symm).trans h

/-- 二段の前合成が同じ作用なら、指定同型の両端も同じ射を回収する。 -/
lemma FunctorIso.precomp_precomp_endpoints {X Y H K : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : H ⟶ X) (q : K ⟶ H) (r : K ⟶ X) (h : q ≫ p = r) :
    ((e.precomp p).precomp q).sourceMap = (e.precomp r).sourceMap ∧
    ((e.precomp p).precomp q).targetMap = (e.precomp r).targetMap := by
  constructor
  · simpa only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.sourceMap, Category.assoc] using congrArg (fun m ↦ m ≫ f) h
  · simpa only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.targetMap, Category.assoc] using congrArg (fun m ↦ m ≫ g) h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (precomp_precomp_endpoints)


/-- 同じ作用での指定値の回収は、二段の前合成の表示でも指定値を保持する。 -/
lemma functorIso_precomp_precomp_of_value_heq {X Y H K : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : H ⟶ X) (q : K ⟶ H) (r : K ⟶ X) (h : q ≫ p = r)
    {a b : K ⟶ Y} (E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (he : HEq (e.precomp r) E) :
    HEq E ((e.precomp p).precomp q) := by
  have hh := HEq.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e p q))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq e h)
  exact HEq.trans he.symm hh.symm

/-- 始点だけの正規化を外しても、前合成した終点は同じ元の終点を回収する。 -/
lemma functorIsoOfEq_precomp_targetMap_recover {X Y K : SSet.{u}}
    {f g f' : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (r : K ⟶ X)
    {a : K ⟶ Y} (h : ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf rfl).precomp r).targetMap = a) :
    r ≫ e.targetMap = a := by
  exact h

/-- 前合成した始点の回収を、同じ元の始点の射として不透明なまま取り出す。 -/
lemma functorIso_precomp_sourceMap_recover {X Y K : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : K ⟶ X) {a : K ⟶ Y}
    (h : (e.precomp r).sourceMap = a) : r ≫ e.sourceMap = a := by
  exact h

/-- 前合成した終点の回収を、同じ元の終点の射として不透明なまま取り出す。 -/
lemma functorIso_precomp_targetMap_recover {X Y K : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : K ⟶ X) {a : K ⟶ Y}
    (h : (e.precomp r).targetMap = a) : r ≫ e.targetMap = a := by
  exact h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
