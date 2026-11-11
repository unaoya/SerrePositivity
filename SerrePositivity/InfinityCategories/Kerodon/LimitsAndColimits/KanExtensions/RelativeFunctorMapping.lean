module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.PathRelativeTargetComparison

/-!
概要：任意の U 上の元の相対 Kan 関手の片側写像空間比較。
方針：path 置換上の比較を元の相対標的との同値で消去する。
規約：U に inner 性や同値持ち上げは要求しない。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の元の相対制限への接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：元の相対制限と切断による path 置換上の制限は可換。
方針：二つの引き戻し射影で比較し、前合成の自然性と切断の合成式を使う。
規約：全単体での射の等式。
使われ方：置換後の写像空間比較の元の相対制限への帰還。 -/
lemma kanPathRelativeTargetComparison_square {K C D E : SSet.{u}}
    (U : D ⟶ E) (δ : K ⟶ C) (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap U)) :
    s.π ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeTargetComparison U δ s t = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeFunctorRestriction U δ t := by
  apply t.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeTargetComparison_fst, ← Category.assoc, s.π_fst]
    change (pre δ).app D ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection U) =
      ((ihom C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection U) ≫ t.π) ≫ t.fst
    rw [Category.assoc, t.π_fst]
    exact ((pre δ).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection U)).symm
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeTargetComparison_snd, s.π_snd]
    change (ihom C).map U =
      ((ihom C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection U) ≫ t.π) ≫ t.snd
    rw [Category.assoc, t.π_snd]
    change (ihom C).map U = (ihom C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection U) ≫
      (ihom C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap U)
    rw [← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map]

/-- 概要：一般 U の相対左 Kan 関手から任意の関手へ出る相対比較はホモトピー同値。
方針：path 置換上の比較から、相対標的間の同値の写像空間作用を消去する。
規約：U の充填性を仮定しない。
使われ方：元の相対制限の左側の片側普遍性。 -/
lemma kanRelativeLeftFunctor_relative_pinchedHomMap_equivalence_general {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (F G : C ⟶ D) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory_of_mono U δ s
  let t := Functor.PullbackObjObj.ofHasPullback internalHom δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap U)
  have : Quasicategory t.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory_of_mono _ _ t
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeLeftFunctor_pinchedHomMap_equivalence δ hδ U t F G hF
  rw [← kanPathRelativeTargetComparison_square U δ s t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeTargetComparison_isQCatEquivalence U δ s t).isFullyFaithful _ _
    |>.cancel_right h

/-- 概要：一般 U の相対右 Kan 関手へ任意の関手から入る相対比較はホモトピー同値。
方針：path 置換上の比較と元の相対標的への同値の消去則を使う。
規約：始点の普遍性と U の充填性は仮定しない。
使われ方：元の相対制限の右側の片側普遍性。 -/
lemma kanRelativeRightFunctor_relative_pinchedHomMap_equivalence_general {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U)
    (F G : C ⟶ D) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory_of_mono U δ s
  let t := Functor.PullbackObjObj.ofHasPullback internalHom δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap U)
  have : Quasicategory t.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory_of_mono _ _ t
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeRightFunctor_pinchedHomMap_equivalence δ hδ U t F G hG
  rw [← kanPathRelativeTargetComparison_square U δ s t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPathRelativeTargetComparison_isQCatEquivalence U δ s t).isFullyFaithful _ _
    |>.cancel_right h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
