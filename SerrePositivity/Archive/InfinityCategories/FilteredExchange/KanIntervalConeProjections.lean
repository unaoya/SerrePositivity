module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：区間引き戻しの native 錐の二脚と元の具体的な射影を照合する。
方針：指定切断との比較を元の始域への射影で後合成する。
規約：頂点の自己同値を挟まない。使われ方：一般 coherent filtered 比較の脚の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : KanObject.{u}}

/-- 概要：native な左脚は元の第一入力への射影にホモトピック。
方針：切断との比較に始域射影を後合成。規約：元の模型。使われ方：左脚の照合。 -/
lemma intervalPullbackConeKanLeg_left (f : X ⟶ Y) (g : Z ⟶ Y) :
    Nonempty (SSet.Homotopy
      (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left))
      (intervalPullbackLeft f g)) := by
  obtain ⟨e⟩ := intervalPullbackConeKanLeg_section f g (AsSmall.up.obj WalkingCospan.left)
  change SSet.Homotopy
    (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left) ≫
      intervalReplacementSection f)
    (pullback.fst (intervalReplacementEndpoint f) g) at e
  have h := functorHomotopyPostcomp e
    (pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f)
  change SSet.Homotopy
    ((intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.left) ≫
      intervalReplacementSection f) ≫
        pullback.snd ((intervalEndpointNatTrans 0).app Y.obj) f)
    (intervalPullbackLeft f g) at h
  rw [Category.assoc, intervalReplacementSection_projection, Category.comp_id] at h
  exact ⟨h⟩

/-- 概要：native な右脚は元の第二入力への射影にホモトピック。
方針：切断の右成分は恒等射。規約：同じ頂点。使われ方：右脚の照合。 -/
lemma intervalPullbackConeKanLeg_right (f : X ⟶ Y) (g : Z ⟶ Y) :
    Nonempty (SSet.Homotopy
      (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right))
      (intervalPullbackRight f g)) := by
  obtain ⟨e⟩ := intervalPullbackConeKanLeg_section f g (AsSmall.up.obj WalkingCospan.right)
  change SSet.Homotopy
    (intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right) ≫ 𝟙 Z.obj)
    (intervalPullbackRight f g) at e
  have hid := Category.comp_id (show (intervalPullbackKanObject f g).obj ⟶ Z.obj from
    intervalPullbackConeKanLeg f g (AsSmall.up.obj WalkingCospan.right))
  exact ⟨{ h := e.h, h₀ := e.h₀.trans hid, h₁ := e.h₁, rel := e.rel }⟩

end SerrePositivity.InfinityCategories.F2
