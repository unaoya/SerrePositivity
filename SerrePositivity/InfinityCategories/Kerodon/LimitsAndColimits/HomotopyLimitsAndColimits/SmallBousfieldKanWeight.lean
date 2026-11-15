module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps

/-!
概要：小さい添字圏の BK 重みを、AsSmall による持ち上げの重みと比較する。
方針：over 圏の射列に AsSmall.down を後合成して ULift に入れる。
規約：全添字射と全単体作用素に自然な指定比較。
使われ方：HA 1.2.4、G10 の係数環の宇宙での native 錐比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable (J : Type) [SmallCategory J]

/-- 持ち上げた over の射列を、元の over の同じ射列へ戻す重みの指定比較。 -/
def smallBousfieldKanWeightDown :
    bousfieldKanWeight (AsSmall.{u} J) ⟶
      AsSmall.down ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{u,0} where
  app j :=
    { app _ := ↾fun s => ULift.up (s ⋙ Over.post (AsSmall.down : AsSmall.{u} J ⥤ J))
      naturality _ _ _ := rfl }
  naturality i j f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
