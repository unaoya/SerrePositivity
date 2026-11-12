module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange

/-!
概要：恒等前合成と、同じ指定単位の左右の自己作用を厳密に計算する。
方針：ホモトピー圏の恒等関手と指定同型の交換則を使う。
規約：指定同型の値を保持。使われ方：指定単位・余単位の第二三角恒等式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 恒等射による前合成は、元の指定関手同型そのものを回収する。 -/
lemma functorIso_precomp_id {X Y : SSet.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    e.precomp (𝟙 X) = e := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  have h : SSet.mapHomotopyCategory ((pre (𝟙 X)).app Y) =
      𝟭 (SSet.HomotopyCategory ((ihom X).obj Y)) := by
    change (hoFunctor.map ((pre (𝟙 X)).app Y)).toFunctor = _
    rw [pre_id, NatTrans.id_app, CategoryTheory.Functor.map_id]
    rfl
  exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq h e)

/-- 同じ恒等射への指定単位の左右の自己作用は、指定同型として一致する。 -/
lemma functorIso_unit_self_whisker {X : SSet.{u}} [Quasicategory X]
    {f : X ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (𝟙 X)) : e.postcomp f = e.precomp f := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange e e
  rw [functorIso_precomp_id, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id] at h
  have hc := congrArg (fun k => k ≪≫ e.symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc

end SerrePositivity.InfinityCategories.Project.FilteredExchange
