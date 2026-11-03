module
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransportAlgebra

public import SerrePositivity.InfinityCategories.Core.CatInfinity.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeImageCommutativity
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ReplacementFunctorIsoSection
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeProjectionIsoTransport

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

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：左脚の像の指定比較と元の第一射影・指定 path の整合。
方針：交換則と切断上の同型の簡約で二つの経路を同定する。
規約：元の指定同型の値と合成の向きを保持する。
使われ方：Cat_∞ 内の引き戻しと全試験関手 core の比較。 -/
lemma catPullbackConeLeftImageIso_path (p : A ⟶ C) (q : B ⟶ C) :
    (catPullbackConeFstIso p q).postcomp p ≪≫
      (equivalencePathReplacementFunctorIso p).precomp
        (pullback.fst (equivalencePathReplacementMap p) q) =
    catPullbackConeLeftImageIso p q := by
  let e := catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)
  change FunctorIso (catPullbackConeFst p q ≫ equivalencePathReplacementSection p)
    (pullback.fst (equivalencePathReplacementMap p) q) at e
  have he := functorIso_whisker_exchange e (equivalencePathReplacementFunctorIso p)
  have hn := equivalencePathReplacementFunctorIso_section_precomp_isFunctorEqIso p
    (catPullbackConeFst p q)
  have hs : (catPullbackConeFst p q ≫ equivalencePathReplacementSection p) ≫
      (equivalencePathReplacementProjection p ≫ p) = catPullbackConeFst p q ≫ p := by
    rw [← Category.assoc, Category.assoc (catPullbackConeFst p q),
      equivalencePathReplacementSection_projection, Category.comp_id]
  have ht : (catPullbackConeFst p q ≫ equivalencePathReplacementSection p) ≫
      equivalencePathReplacementMap p = catPullbackConeFst p q ≫ p := by
    rw [Category.assoc, equivalencePathReplacementSection_map]
  have h := functorIso_source_transport_square _ _ _ _ hs ht hn he
  have hf : (catPullbackConeFst p q ≫ equivalencePathReplacementSection p) ≫
      equivalencePathReplacementProjection p = catPullbackConeFst p q := by
    rw [Category.assoc, equivalencePathReplacementSection_projection, Category.comp_id]
  have hh := functorIso_postcomp_heq_of_heq (e.postcomp (equivalencePathReplacementProjection p))
    (catPullbackConeFstIso p q) hf rfl (catPullbackConeFstIso_heq p q) p
  have hh' : HEq ((catPullbackConeFstIso p q).postcomp p)
      (e.postcomp (equivalencePathReplacementProjection p ≫ p)) :=
    hh.trans (heq_of_eq (functorIso_postcomp_postcomp e _ _))
  have ha : functorIsoOfEq (e.postcomp (equivalencePathReplacementProjection p ≫ p)) hs rfl =
      (catPullbackConeFstIso p q).postcomp p :=
    eq_of_heq ((functorIsoOfEq_heq _ _ _).trans hh'.symm)
  exact (congrArg (fun t ↦ t ≪≫ (equivalencePathReplacementFunctorIso p).precomp
    (pullback.fst (equivalencePathReplacementMap p) q)) ha).symm.trans h

end SerrePositivity.InfinityCategories.F2
