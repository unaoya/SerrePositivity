module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerCancellation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection


/-!
概要：前合成で回収される指定同型は、任意の元の作用でさらに前合成しても回収される。
方針：同型の前合成の合成則と同じ回収等式への作用を組み合わせる。
規約：指定された同型と端点正規化の値を保持する。
使われ方：第二面の分解比較を元の大域 Hom 作用へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 前合成による指定値の回収とさらに前合成した端点正規化を合成する。 -/
lemma functorIso_precomp_of_projection_heq {H X Y K : SSet.{u}}
    {F G : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (p : H ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p ≫ F) (p ≫ G)) (hp : e.precomp p = d)
    {f g : H ⟶ Y} (d₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : K ⟶ H)
    (hd : HEq (d.precomp r) (d₀.precomp r)) :
    HEq (e.precomp (r ≫ p)) (d₀.precomp r) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e p r
  have hh := congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp v r) hp
  exact (heq_of_eq hc.symm).trans ((heq_of_eq hh).trans hd)

/-- 前合成の端点正規化後にさらに前合成すると、同じ合成した作用を回収する。 -/
lemma functorIsoOfEq_precomp_precomp_heq {H X Y K : SSet.{u}}
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : H ⟶ X)
    {f' g' : H ⟶ Y} (hf : p ≫ f = f') (hg : p ≫ g = g') (r : K ⟶ H) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.precomp p) hf hg).precomp r) (e.precomp (r ≫ p)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_heq (e.precomp p) hf hg r).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e p r))

/-- 後合成の端点正規化を前合成すると、元の前後合成された指定値を回収する。 -/
lemma functorIsoOfEq_postcomp_precomp_heq {H X Y K : SSet.{u}}
    {f g : H ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : X ⟶ Y)
    {f' g' : H ⟶ Y} (hf : f ≫ p = f') (hg : g ≫ p = g') (r : K ⟶ H) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.postcomp p) hf hg).precomp r)
      ((e.precomp r).postcomp p) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_precomp_heq (e.postcomp p) hf hg r).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp e r p).symm)

/-- 前合成した同型の端点正規化が指定値なら、前後合成の交換後も同じ指定値。 -/
lemma functorIsoOfEq_precomp_postcomp_heq_of_eq {H X Y K : SSet.{u}}
    {f g : H ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : K ⟶ H)
    {f' g' : K ⟶ X} (hf : r ≫ f = f') (hg : r ≫ g = g')
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.precomp r) hf hg = d) (p : X ⟶ Y) :
    HEq ((e.postcomp p).precomp r) (d.postcomp p) := by
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp e r p).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq_of_eq (e.precomp r) hf hg d hd p).symm

/-- 同じ合成作用を与える二つの前合成の分解は、指定同型の同じ値を回収する。 -/
lemma functorIso_precomp_square_heq {H₀ H₁ X Y K : SSet.{u}}
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (p₀ : H₀ ⟶ X) (r₀ : K ⟶ H₀) (p₁ : H₁ ⟶ X) (r₁ : K ⟶ H₁)
    (h : r₀ ≫ p₀ = r₁ ≫ p₁) :
    HEq ((e.precomp p₀).precomp r₀) ((e.precomp p₁).precomp r₁) := by
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e p₀ r₀)).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq e h).trans
      (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e p₁ r₁).symm))

/-- 前合成した指定値の同定は、同じ後合成と前後合成の交換を保持する。 -/
lemma functorIso_postcomp_precomp_of_heq {H X Y K : SSet.{u}}
    {f g : H ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (r : K ⟶ H)
    {f' g' : K ⟶ X} (hf : r ≫ f = f') (hg : r ≫ g = g')
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hd : HEq d (e.precomp r)) (p : X ⟶ Y) :
    HEq ((e.postcomp p).precomp r) (d.postcomp p) := by
  exact HEq.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp e r p).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq (e.precomp r) d hf hg hd p).symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
