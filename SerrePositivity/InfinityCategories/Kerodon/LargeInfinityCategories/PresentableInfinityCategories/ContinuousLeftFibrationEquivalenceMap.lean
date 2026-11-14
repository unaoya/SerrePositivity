module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.PrecompositionCofinality

/-!
概要：元の連続left-fibration置換は、同じ底上のcofinal射を前合成同値へ送る。
方針：元の単位の自然性、cofinal性の合成・消去則と同じ底上の検出を合成する。
規約：元の置換関手とその単位を使い、比較を選び直さない。
使われ方：全要素圏の同じGrothendieck表示をnativeな全分類へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 元の置換は、底上の同じcofinal射を元の射の前合成同値へ送る。 -/
theorem continuousLeftFibrationReplacement_map_isPrecompositionEquivalence_of_leftCofinal
    {B : SSet.{u}} [Quasicategory B] {X Y : Over B} (f : X ⟶ Y)
    (hc : IsLeftCofinal f.left) :
    IsPrecompositionEquivalence ((continuousLeftFibrationReplacement B).map f).left := by
  have huX := isLeftCofinal_of_leftAnodyne _ (continuousLeftFibrationReplacementUnit_leftAnodyne X)
  have huY := isLeftCofinal_of_leftAnodyne _ (continuousLeftFibrationReplacementUnit_leftAnodyne Y)
  have hn := congrArg (fun g => g.left) ((continuousLeftFibrationReplacementUnit B).naturality f)
  change f.left ≫ ((continuousLeftFibrationReplacementUnit B).app Y).left =
    ((continuousLeftFibrationReplacementUnit B).app X).left ≫
      ((continuousLeftFibrationReplacement B).map f).left at hn
  have hm : IsLeftCofinal ((continuousLeftFibrationReplacement B).map f).left := by
    apply huX.cancel_left
    rw [← hn]
    exact hc.comp huY
  exact isPrecompositionEquivalence_of_leftCofinal_overLeftFibrations _ _
    ((continuousLeftFibrationReplacement B).map f).left
    ((continuousLeftFibrationReplacement B).map f).w hm

/-- 準圏を標的とする底上の前合成同値は、同じ元の置換後も前合成同値。 -/
theorem continuousLeftFibrationReplacement_map_isPrecompositionEquivalence
    {B : SSet.{u}} [Quasicategory B] {X Y : Over B} [Quasicategory Y.left]
    (f : X ⟶ Y) (hf : IsPrecompositionEquivalence f.left) :
    IsPrecompositionEquivalence ((continuousLeftFibrationReplacement B).map f).left :=
  continuousLeftFibrationReplacement_map_isPrecompositionEquivalence_of_leftCofinal f
    (isLeftCofinal_of_precompositionEquivalence f.left hf)
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
