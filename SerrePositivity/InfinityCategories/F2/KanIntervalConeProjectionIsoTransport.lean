module

public import SerrePositivity.InfinityCategories.F2.KanIntervalConeProjectionIsos

/-!
概要：区間錐の指定射影同型と元の脚比較の端点輸送前の値を同定する。
方針：構成時の等式による型の輸送を外す。
規約：指定値を保持。使われ方：元の path と射影比較の最終整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : KanObject.{u}}

/-- 概要：第一射影の指定同型は元の脚比較の後合成の値を保持。
方針：端点輸送の除去。規約：型付きの一致。使われ方：交換則の第一入力。 -/
lemma intervalPullbackConeFstIso_heq (f : X ⟶ Y) (g : Z ⟶ Y) :
    HEq (intervalPullbackConeFstIso f g)
      ((intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.left)).postcomp
        (pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f)) := by
  simp only [intervalPullbackConeFstIso, Eq.mp, _root_.id_eq]
  simp only [eqRec_heq_iff]
  rfl

/-- 概要：第二射影の指定同型は元の脚比較の値を保持。
方針：端点輸送の除去。規約：型付きの一致。使われ方：右脚の像の比較。 -/
lemma intervalPullbackConeSndIso_heq (f : X ⟶ Y) (g : Z ⟶ Y) :
    HEq (intervalPullbackConeSndIso f g)
      (intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.right)) := by
  let e := intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.right)
  change FunctorIso
    (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right) ≫ 𝟙 Z.obj)
    (intervalPullbackRight f g) at e
  exact functorIsoOfEq_heq e
    (Category.comp_id (show (intervalPullbackKanObject f g).obj ⟶ Z.obj from
      intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right))) rfl

end SerrePositivity.InfinityCategories.F2
