module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftHornCellStep
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：底を固定した左ホーン付加の可算反復と、その連続な余極限関手。
方針：恒等関手から左ホーン付加を反復し、底上の関手圏で余極限を取る。
規約：left fibration 性と単位の左アノダイン性は、別途証明する。
使われ方：一般の前層の有限生成模型に用いる具体的な置換。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 左ホーン付加を有限回反復する、底上の関手。 -/
def leftHornCellStage (B : SSet.{u}) : ℕ → (Over B ⥤ Over B)
  | 0 => 𝟭 (Over B)
  | n + 1 => leftHornCellStage B n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellStep B

/-- 底を保つ各反復段の後続射。 -/
def leftHornCellStageMap (B : SSet.{u}) (n : ℕ) :
    leftHornCellStage B n ⟶ leftHornCellStage B (n + 1) :=
  Functor.whiskerLeft (leftHornCellStage B n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellStepUnit B)

/-- 同じ宇宙の可算添字上の、底上の全反復図式。 -/
def leftHornCellSequence (B : SSet.{u}) : AsSmall.{u} ℕ ⥤ Over B ⥤ Over B :=
  AsSmall.down ⋙ Functor.ofSequence (leftHornCellStageMap B)

/-- 左ホーン付加の可算反復の、底上の余極限関手。 -/
def continuousLeftFibrationReplacement (B : SSet.{u}) : Over B ⥤ Over B :=
  colimit (leftHornCellSequence B)

/-- 元の同じ底上の対象から反復の余極限への自然な射。 -/
def continuousLeftFibrationReplacementUnit (B : SSet.{u}) :
    𝟭 (Over B) ⟶ continuousLeftFibrationReplacement B :=
  colimit.ι (leftHornCellSequence B) (AsSmall.up.obj 0)

/-- 各有限反復段は filtered 余極限を保つ。 -/
instance leftHornCellStage_preservesFilteredColimits (B : SSet.{u}) (n : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} (leftHornCellStage B n) := by
  induction n with
  | zero => change PreservesFilteredColimitsOfSize.{u, u} (𝟭 (Over B)); infer_instance
  | succ n ih =>
    change PreservesFilteredColimitsOfSize.{u, u} (leftHornCellStage B n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellStep B)
    infer_instance

/-- 具体的な可算反復の余極限関手は filtered 余極限を保つ。 -/
instance continuousLeftFibrationReplacement_preservesFilteredColimits (B : SSet.{u}) :
    PreservesFilteredColimitsOfSize.{u, u} (continuousLeftFibrationReplacement B) := by
  have : ∀ n, PreservesFilteredColimitsOfSize.{u, u} ((leftHornCellSequence B).obj n) := by
    intro n
    change PreservesFilteredColimitsOfSize.{u, u} (leftHornCellStage B (AsSmall.down.obj n))
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.over_preservesFilteredColimits_colimit_of_pointwise (leftHornCellSequence B)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
