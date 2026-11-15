module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import Mathlib.CategoryTheory.Types.Basic

/-!
概要：元のBK重みのAsSmall・ULiftによる宇宙変更を、指定したdownを順射とする同型にする。
方針：同じover列を指定upで戻し、元の対象・射・構造射の両合成を確認する。
規約：IS-W2 R02〜R03の係数の宇宙移送則。小さい基底宇宙を0に固定しない。
使われ方：元のBK切断を、全Hom∞比較の同じ持ち上げた添字へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory
variable (J : Type u) [SmallCategory J]

/-- 指定downに対する同じover列のupによる持ち上げ。 -/
def bousfieldKanUniverseOverLift (j : AsSmall.{v} J) :
    Over ((AsSmall.down : AsSmall.{v} J ⥤ J).obj j) ⥤ Over j where
  obj f := Over.mk (show ((AsSmall.up : J ⥤ AsSmall.{v} J).obj f.left) ⟶ j from
    (AsSmall.up : J ⥤ AsSmall.{v} J).map f.hom)
  map a := Over.homMk ((AsSmall.up : J ⥤ AsSmall.{v} J).map a.left)
    (by apply ULift.ext; exact Over.w a)
  map_id f := by apply Over.OverMorphism.ext; rfl
  map_comp a b := by apply Over.OverMorphism.ext; rfl

/-- 同じover持ち上げを指定downで戻すと恒等関手。 -/
theorem bousfieldKanUniverseOverLift_down (j : AsSmall.{v} J) :
    bousfieldKanUniverseOverLift J j ⋙ Over.post (AsSmall.down : AsSmall.{v} J ⥤ J) = 𝟭 _ := rfl

/-- 指定downの後で同じover持ち上げをすると恒等関手。 -/
theorem bousfieldKanUniverseOverDown_lift (j : AsSmall.{v} J) :
    Over.post (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanUniverseOverLift J j = 𝟭 _ := rfl

/-- 元のBK重みを指定downと同じULiftで読む自然変換。 -/
def bousfieldKanUniverseWeightDown : bousfieldKanWeight (AsSmall.{v} J) ⟶
    (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u} where
  app j :=
    { app _ := ↾fun s => ULift.up (s ⋙ Over.post (AsSmall.down : AsSmall.{v} J ⥤ J))
      naturality _ _ _ := rfl }
  naturality i j f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    rfl

/-- 元の指定downは、すべての評価と全次数で可逆。 -/
instance bousfieldKanUniverseWeightDown_isIso : IsIso (bousfieldKanUniverseWeightDown.{u,v} J) := by
  haveI (j : AsSmall.{v} J) : IsIso ((bousfieldKanUniverseWeightDown.{u,v} J).app j) := by
    haveI (n : SimplexCategoryᵒᵖ) : IsIso (((bousfieldKanUniverseWeightDown.{u,v} J).app j).app n) := by
      let e : ((bousfieldKanWeight (AsSmall.{v} J)).obj j).obj n ≃
          (((AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanWeight J ⋙
            SSet.uliftFunctor.{max u v,u}).obj j).obj n :=
        { toFun s := ULift.up (s ⋙ Over.post (AsSmall.down : AsSmall.{v} J ⥤ J))
          invFun s := s.down ⋙ bousfieldKanUniverseOverLift J j
          left_inv s := by
            change (s ⋙ Over.post (AsSmall.down : AsSmall.{v} J ⥤ J)) ⋙
              bousfieldKanUniverseOverLift J j = s
            erw [Functor.assoc, bousfieldKanUniverseOverDown_lift, Functor.comp_id]
          right_inv s := by
            apply ULift.ext
            change (s.down ⋙ bousfieldKanUniverseOverLift J j) ⋙
              Over.post (AsSmall.down : AsSmall.{v} J ⥤ J) = s.down
            erw [Functor.assoc, bousfieldKanUniverseOverLift_down, Functor.comp_id] }
      exact (isIso_iff_bijective _).mpr e.bijective
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- 順射を変えずに得る、同じBK重みの宇宙変更の同型。 -/
def bousfieldKanUniverseWeightIso : bousfieldKanWeight (AsSmall.{v} J) ≅
    (AsSmall.down : AsSmall.{v} J ⥤ J) ⋙ bousfieldKanWeight J ⋙ SSet.uliftFunctor.{max u v,u} :=
  asIso (bousfieldKanUniverseWeightDown J)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
