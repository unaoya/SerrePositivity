module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftHornCellData

/-!
概要：底上の全左ホーンを一段付加する、filtered 余極限を保つ具体的な関手。
方針：有限ホーンのコピーの余積と評価射の pushout を、底上の関手圏で取る。
規約：置換の存在や連続性を仮定せず、一段の関手を実際に構成する。
使われ方：left fibration 置換の可算反復。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 全左ホーンの始域のコピーは filtered 余極限を保つ。 -/
instance leftHornSourceCopies_preservesFilteredColimits (B : SSet.{u}) :
    PreservesFilteredColimitsOfSize.{u, u} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornSourceCopies B) := by
  let D := Discrete.functor (fun h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftHornCellIndex B ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSource h) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSource h))
  have : ∀ h, PreservesFilteredColimitsOfSize.{u, u} (D.obj h) := by
    intro h
    change PreservesFilteredColimitsOfSize.{u, u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSource h.as) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSource h.as))
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.over_preservesFilteredColimits_colimit_of_pointwise D

/-- 全左ホーンの終域のコピーは filtered 余極限を保つ。 -/
instance leftHornTargetCopies_preservesFilteredColimits (B : SSet.{u}) :
    PreservesFilteredColimitsOfSize.{u, u} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornTargetCopies B) := by
  let D := Discrete.functor (fun h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftHornCellIndex B ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSource h) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellTarget h))
  have : ∀ h, PreservesFilteredColimitsOfSize.{u, u} (D.obj h) := by
    intro h
    change PreservesFilteredColimitsOfSize.{u, u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellSource h.as) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCellTarget h.as))
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.over_preservesFilteredColimits_colimit_of_pointwise D

/-- 固定した底上の全左ホーンを一段付加する。 -/
def leftHornCellStep (B : SSet.{u}) : Over B ⥤ Over B :=
  pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesEvaluation B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesBoundary B)

/-- 元の対象から一段の付加への、底を保つ自然な射。 -/
def leftHornCellStepUnit (B : SSet.{u}) : 𝟭 (Over B) ⟶ leftHornCellStep B :=
  pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesEvaluation B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesBoundary B)

/-- 付加した全標準単体から一段の付加への、底を保つ射。 -/
def leftHornCellStepCells (B : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornTargetCopies B ⟶ leftHornCellStep B :=
  pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesEvaluation B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesBoundary B)

/-- 各セルの境界と元の評価射の厳密な可換性。 -/
lemma leftHornCellStep_condition (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesEvaluation B ≫ leftHornCellStepUnit B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesBoundary B ≫ leftHornCellStepCells B :=
  pushout.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesEvaluation B) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesBoundary B)

/-- この具体的な一段の左ホーン付加関手は filtered 余極限を保つ。 -/
instance leftHornCellStep_preservesFilteredColimits (B : SSet.{u}) :
    PreservesFilteredColimitsOfSize.{u, u} (leftHornCellStep B) := by
  have : ∀ j, PreservesFilteredColimitsOfSize.{u, u}
      ((span (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesEvaluation B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesBoundary B)).obj j) := by
    intro j
    cases j with
    | none =>
      change PreservesFilteredColimitsOfSize.{u, u} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornSourceCopies B)
      infer_instance
    | some k =>
      cases k with
      | left =>
        change PreservesFilteredColimitsOfSize.{u, u} (𝟭 (Over B))
        infer_instance
      | right =>
        change PreservesFilteredColimitsOfSize.{u, u} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornTargetCopies B)
        infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.over_preservesFilteredColimits_colimit_of_pointwise
    (span (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesEvaluation B) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftHornCopiesBoundary B))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
