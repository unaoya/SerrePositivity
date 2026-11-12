module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeImageCommutativity
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalReplacementPathIsoSection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeProjectionIsoTransport

/-!
概要：左脚の像の指定比較と元の第一射影・指定 path の整合。
方針：交換則と切断上の同型の簡約で二つの経路を同定する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {X Y Z : KanObject.{u}}
/-- 概要：左脚の像の指定比較と元の第一射影・指定 path の整合。
方針：交換則と切断上の同型の簡約で二つの経路を同定する。
規約：元の指定同型の値と合成の向きを保持する。
使われ方：𝒮 の引き戻しと元の全 path の比較。 -/
lemma intervalPullbackConeLeftImageIso_path (f : X ⟶ Y) (g : Z ⟶ Y) :
    (intervalPullbackConeFstIso f g).postcomp f ≪≫
      (intervalReplacementPathIso f).precomp
        (pullback.fst (intervalReplacementEndpoint f) g) =
    intervalPullbackConeLeftImageIso f g := by
  let l : (intervalPullbackKanObject f g).obj ⟶ X.obj :=
    intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left)
  let e := intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.left)
  change FunctorIso (l ≫ intervalReplacementSection f)
    (pullback.fst (intervalReplacementEndpoint f) g) at e
  have he := functorIso_whisker_exchange e (intervalReplacementPathIso f)
  have hn := intervalReplacementPathIso_section_precomp_isFunctorEqIso f
    (l)
  have hs : (l ≫ intervalReplacementSection f) ≫
      (pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f ≫ f) = l ≫ f := by
    rw [← Category.assoc, Category.assoc (l),
      intervalReplacementSection_projection, Category.comp_id]
  have ht : (l ≫ intervalReplacementSection f) ≫
      intervalReplacementEndpoint f = l ≫ f := by
    rw [Category.assoc, intervalReplacementSection_endpoint]
  have h := functorIso_source_transport_square _ _ _ _ hs ht hn he
  have hf : (l ≫ intervalReplacementSection f) ≫
      pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f = l := by
    rw [Category.assoc, intervalReplacementSection_projection, Category.comp_id]
  have hh := functorIso_postcomp_heq_of_heq
    (e.postcomp (pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f))
    (intervalPullbackConeFstIso f g) hf rfl (intervalPullbackConeFstIso_heq f g) f
  have hh' : HEq ((intervalPullbackConeFstIso f g).postcomp f)
      (e.postcomp (pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f ≫ f)) :=
    hh.trans (heq_of_eq (functorIso_postcomp_postcomp e _ _))
  have ha : functorIsoOfEq
      (e.postcomp (pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f ≫ f)) hs rfl =
      (intervalPullbackConeFstIso f g).postcomp f :=
    eq_of_heq ((functorIsoOfEq_heq _ _ _).trans hh'.symm)
  exact (congrArg (fun t ↦ t ≪≫ (intervalReplacementPathIso f).precomp
    (pullback.fst (intervalReplacementEndpoint f) g)) ha).symm.trans h

end SerrePositivity.InfinityCategories.F2
