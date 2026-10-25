module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallWeightedSectionsContinuity
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
概要：有限重みと有限な end 添字の weighted sections は filtered 余極限を保つ。
方針：有限内部 Hom の保存と、通常の有限極限の次数ごとの交換を合成する。
規約：濃度変更境界を使わず、元の weighted sections 関手を保持する。
使われ方：I-2 d′ の有限 poset の Bousfield–Kan 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open Presentable HomotopyLimits

/-- 有限重みの元の end 図式は、各成分で filtered 余極限を保つ。 -/
lemma finiteWeightedEndDiagram_preservesFilteredColimits
    {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u})
    (hW : ∀ i, (W.obj i).Finite) (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (weightedEndDiagramFunctor W) := by
  have (i : I) : PreservesColimitsOfShape J (ihom (W.obj i)) := by
    have := hW i
    infer_instance
  apply preservesColimitsOfShape_of_evaluation
  intro x
  cases x with
  | left i =>
    exact inferInstanceAs (PreservesColimitsOfShape J
      (((evaluation I SSet.{u}).obj i) ⋙ ihom (W.obj i)))
  | right f =>
    exact inferInstanceAs (PreservesColimitsOfShape J
      (((evaluation I SSet.{u}).obj f.right) ⋙ ihom (W.obj f.left)))

/-- 有限重み・有限全射添字の元の weighted sections は filtered 余極限を保つ。 -/
lemma finiteWeightedSections_preservesFilteredColimits
    {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u})
    (hW : ∀ i, (W.obj i).Finite) (hI : HasCardinalLT (Arrow I) Cardinal.aleph0.{u})
    (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (weightedSectionsFunctor W) := by
  let : Fact (Cardinal.aleph0.{u}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : IsCardinalFiltered J Cardinal.aleph0.{u} := (isCardinalFiltered_aleph0_iff J).mpr
    inferInstance
  have := finiteWeightedEndDiagram_preservesFilteredColimits W hW J
  have := smallSSetLimit_preservesCardinalFilteredColimits
    (WalkingMulticospan (multicospanShapeEnd I)) (hasCardinalLT_endIndex_arrow le_rfl I hI) J
  have : PreservesColimitsOfShape J (weightedEndDiagramFunctor W ⋙ lim) := inferInstance
  exact preservesColimitsOfShape_of_natIso (weightedSectionsLimitIso W).symm

end SerrePositivity.InfinityCategories.F2.Ind
