module

public import SerrePositivity.KST.NonConnective.SequentialLevelHomLimit

/-!
概要：逐次 Hom 極限の普遍族を全スペクトルへ束ねるための境界比較。
方針：suspension の全 Hom 作用の反変自然性を閉構造から証明する。
規約：単射性や Ω 条件を自然性の仮定に加えない。
使われ方：K-7 の全 Raw Hom 極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- suspension の全 Hom 作用は、元の点つき源の制限と厳密に可換。 -/
lemma sequentialSuspensionHom_pre {X Z Y : PointedSimplicialSet.{u}} (i : X ⟶ Z) :
    (MonoidalClosed.pre i).app Y ≫ suspensionHom X Y =
      suspensionHom Z Y ≫ (MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ i)).app
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) := by
  unfold suspensionHom
  rw [← curry_natural_left, curry_pre_app]
  apply congrArg curry
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp,
    id_tensor_pre_app_comp_ev, whiskerLeft_comp, ← associator_naturality_middle_assoc]
  rfl

/-- 元の Raw Hom の境界比較も、BF 源の各段の制限と厳密に可換。 -/
lemma sequentialRawStep_pre {X Z : OmegaSpectrum.{u}} (f : X ⟶ Z)
    (Y : KanSequence.{u}) (k : ℕ) :
    RawSpectrumMapping.step Z Y k ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ f.app k) (Y.level (k + 1)).space =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f.app k) (Y.level k).space ≫ RawSpectrumMapping.step X Y k := by
  have h : (suspensionHom (Z.level k).space (Y.level k).space ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Z.level k).space)).map (Y.sigma k)) ≫
        (MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ f.app k)).app
          (Y.level (k + 1)).space =
      (MonoidalClosed.pre (f.app k)).app (Y.level k).space ≫
        (suspensionHom (X.level k).space (Y.level k).space ≫
          (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level k).space)).map (Y.sigma k)) := by
    rw [Category.assoc, ← pre_comm_ihom_map, ← Category.assoc,
      ← sequentialSuspensionHom_pre, Category.assoc]
  have hp := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre
    (PointedSimplicialSet.circle.{u} ◁ f.app k) (Y.level (k + 1)).space
  have hq := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre (f.app k) (Y.level k).space
  have hr := congrArg Under.Hom.right h
  change _ ≫ ((MonoidalClosed.pre (PointedSimplicialSet.circle.{u} ◁ f.app k)).app
    (Y.level (k + 1)).space).right =
      ((MonoidalClosed.pre (f.app k)).app (Y.level k).space).right ≫ _ at hr
  exact ((congrArg (RawSpectrumMapping.step Z Y k ≫ ·)
    (congrArg Under.Hom.right hp)).trans hr).trans
      (congrArg (· ≫ RawSpectrumMapping.step X Y k) (congrArg Under.Hom.right hq)).symm

/-- 点つき源の制限の合成を、同じ基礎単体集合の射として保持する。 -/
lemma sequentialPointedPre_comp {A B C : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (f ≫ g) Y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre g Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f Y :=
  (congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp f g Y)).symm

end SerrePositivity.KST.NonConnective
