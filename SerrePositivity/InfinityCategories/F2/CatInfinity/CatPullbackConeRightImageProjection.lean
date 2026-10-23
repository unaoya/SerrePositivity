module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeImageIsos
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeProjectionIsoTransport
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransportAlgebra

/-!
概要：右脚の像の指定比較と元の第二射影の比較の整合。
方針：引き戻しの可換等式による端点の輸送を戻す。
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
/-- 概要：右脚の像の指定比較と元の第二射影の比較の整合。
方針：引き戻しの可換等式による端点の輸送を戻す。
規約：元の指定同型の値と合成の向きを保持する。
使われ方：Cat_∞ 内の引き戻しと全試験関手 core の比較。 -/
lemma catPullbackConeRightImageIso_projection (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackConeRightImageIso p q ≪≫
      functorEqIso (pullback.condition (f := equivalencePathReplacementMap p) (g := q)) =
    (catPullbackConeSndIso p q).postcomp q := by
  let e := catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)
  have hs : catPullbackConeSnd p q ≫ 𝟙 B = catPullbackConeSnd p q := Category.comp_id _
  have hh := functorIso_postcomp_heq_of_heq e (catPullbackConeSndIso p q) hs rfl
    (catPullbackConeSndIso_heq p q) q
  have h := functorIsoOfEq_trans_eqIso (e.postcomp q)
    (congrArg (fun k ↦ k ≫ q) hs)
    (pullback.condition (f := equivalencePathReplacementMap p) (g := q)).symm
  exact h.trans (eq_of_heq ((functorIsoOfEq_heq _ _ _).trans hh.symm))

end SerrePositivity.InfinityCategories.F2
