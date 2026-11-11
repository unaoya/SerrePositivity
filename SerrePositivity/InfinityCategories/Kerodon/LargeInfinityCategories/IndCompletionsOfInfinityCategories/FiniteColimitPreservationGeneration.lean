module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservedPushoutShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PreservedColimitBasicShapes
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapeInduction

/-!
概要：空図式と点 span の余極限保存から、全有限単体集合形状の保存を導く。
方針：同じ全余錐が元の圏と像の圏で普遍的という述語を、有限セルで帰納する。
規約：存在だけの有限生成に弱めず、元の任意の指定余極限全余錐を保存する。
使われ方：I-2 d′ の全有限形状に対する coherent 交換の帰納。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 空形状と点 span の保存された全余錐から、全有限形状の保存を生成する。 -/
lemma hasPreservedColimit_finite_of_empty_pointSpan {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (he : ∀ (T : SSet.{u}) (p : (⊥ : T.Subcomplex).toSSet ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U p)
    (hs : ∀ p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u} ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U p)
    (K : SSet.{u}) [K.Finite] (p : K ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U p := by
  have h : ∀ q : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U q :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.finiteShape_induction_of_pushouts (fun A ↦ ∀ q : A ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U q)
      (fun e ih q ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_restrict_isIso U q e.hom).mpr (ih _))
      he (fun n q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_of_terminalShapeVertex U q _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.stdSimplex_last_isTerminalVertex n)) (by
        intro A B C D f g i j _ hp hA hB hC q
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_restrict_isIso U q hp.isoPushout.inv).mpr
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasPreservedColimit_pushout_shape U f g (hp.isoPushout.inv ≫ q)
          (hA _) (hB _) (hC _) hs) K
  exact h p

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
