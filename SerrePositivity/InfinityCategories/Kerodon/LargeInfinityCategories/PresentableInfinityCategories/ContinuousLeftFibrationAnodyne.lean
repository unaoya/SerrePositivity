module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationFilling
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftHornCellAnodyne

/-!
概要：連続 left fibration 置換の元の単位は、全空間で左アノダインである。
方針：評価と忘却で同じ可算余極限を保ち、各後続段の左アノダイン性を超限合成する。
規約：置換と単位は元の具体的な関手から変更しない。
使われ方：元の底上の相対 Hom と置換後の相対 Hom の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の単位の全空間の射を、実際の左アノダイン射の可算超限合成で表示する。 -/
def continuousLeftFibrationReplacementUnit_leftAnodyneComposition {B : SSet.{u}}
    (X : Over B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.TransfiniteCompositionOfShape ℕ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit B).app X).left := by
  let e := (evaluation (Over B) (Over B)).obj X
  let c := (colimit.cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSequence B)).whisker AsSmall.up
  let d := (Over.forget B).mapCocone (e.mapCocone c)
  refine {
    F := AsSmall.up ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSequence B ⋙ e ⋙ Over.forget B
    isoBot := Iso.refl _
    incl := d.ι
    isColimit := isColimitOfPreserves (Over.forget B)
      (isColimitOfPreserves e
        ((colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSequence B)).whiskerEquivalence AsSmall.equiv))
    fac := by rfl
    map_mem := ?_ }
  intro j _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions
    (((Functor.ofSequence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellStageMap B)).map
      (homOfLE (Nat.le_succ j))).app X).left
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellStepUnit_leftAnodyne ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellStage B j).obj X)

/-- 具体的な連続置換への底上の単位は、全空間で左アノダイン。 -/
lemma continuousLeftFibrationReplacementUnit_leftAnodyne {B : SSet.{u}} (X : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationReplacementUnit B).app X).left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.transfiniteCompositionsOfShape_le ℕ _
    (continuousLeftFibrationReplacementUnit_leftAnodyneComposition X).mem

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
