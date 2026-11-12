module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnstraighteningLimitConeLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.EquivalenceSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening

/-!
概要：小さい対象族上の空間値関手の解図式と、その極限上の全解錐を構成する。
方針：制限関手の小さい unstraightening を元の圏へ送り、極限保存から全錐を持ち上げる。
規約：生成性や accessibility はこの幾何的な構成の仮定に含めない。
使われ方：accessible かつ小極限保存な関手の余表現可能性の解対象。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {A : SSet.{u}} {C : SSet.{u + 1}}
  (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：小さい対象族上の全解を元の圏に送る小さい図式。
方針：元の制限関手の小さい left unstraightening の射影を対象族へ合成する。
規約：解の高次単体を含む全添字を保持する。
使われ方：解対象の極限の添字図式。 -/
def smallSolutionDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (i ≫ F)) ⟶ C :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (i ≫ F)) ≫ i

/-- 概要：小さい全解図式を元の F の unstraightening へ同時に持ち上げる。
方針：元の縮小同型と底変換の全空間比較を合成する。
規約：各点の解を独立に選ばず、元の全関手を構成する。
使われ方：極限上の全解錐を持ち上げる始域図式。 -/
def smallSolutionLift :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (i ≫ F)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso (i ≫ F)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap (i ≫ F) F i rfl

/-- 概要：全解の持ち上げは元の小さい解図式を厳密に被覆する。
方針：縮小同型と底変換比較の射影の式を合成する。
規約：元の対象族 i を保持する。
使われ方：元の極限錐を同じ全空間上に持ち上げる条件。 -/
lemma smallSolutionLift_projection :
    smallSolutionLift i F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F = smallSolutionDiagram i F := by
  rw [smallSolutionLift, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMap_projection,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection]
  rfl

/-- 概要：小極限を保つ空間値関手の小さい全解図式は元の極限上の全解錐を持つ。
方針：底の極限を取り、その F 像の極限性から元の unstraightening に錐を持ち上げる。
規約：解対象の始対象性や余表現可能性はこの補題では主張しない。
使われ方：後続の compact 表示への因子化と retract の構成。 -/
lemma exists_smallSolutionCone (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits C) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallLimits F) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (smallSolutionDiagram i F), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧
      ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (smallSolutionLift i F),
        d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F = c.val := by
  obtain ⟨c, hc⟩ := hC _ (smallSolutionDiagram i F)
  let c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (smallSolutionLift i F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) :=
    ⟨c.val, by rw [smallSolutionLift_projection]; exact c.property⟩
  have hcF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F c₀) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F c₀) rfl).mp
      (hF _ (smallSolutionDiagram i F) c hc)
  obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_unstraighteningCone_lift_of_map_isLimit F
    (smallSolutionLift i F) c₀ hcF
  exact ⟨c, hc, d, hd⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
