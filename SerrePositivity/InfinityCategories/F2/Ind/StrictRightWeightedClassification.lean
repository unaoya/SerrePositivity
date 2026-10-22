module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictLeftWeightedClassification
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOppositeDiagram
public import SerrePositivity.InfinityCategories.F1.RightStraighteningInfinityEquivalence

/-!
概要：元の strict right fibration 図式を、共同 weighted left 分類と全添字上で比較する。
方針：各係数の反転を通常図式にまとめ、実際の反転との大域比較を合成する。
規約：元の全高次の分類作用を保持。使われ方：weighted 密度の右制限の大域同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の right 図式の反転係数を持つ共同 weighted 分類。 -/
def strictRightWeightedClassification :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C :=
  strictLeftWeightedClassification (F ⋙ rightFibrationOppositeOrdinary C)

/-- 共同 weighted 分類は、元の right straightening の全図式と一つの関手同型を持つ。 -/
def strictRightWeightedClassificationIso :
    FunctorIso (strictRightWeightedClassification F)
      (HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C) := by
  have hr := (strictRightFibrationOppositeDiagramIso F).postcomp
    (leftStraighteningInfinityMap C.op)
  exact strictLeftWeightedClassificationIso (F ⋙ rightFibrationOppositeOrdinary C) ≪≫ hr.symm

end SerrePositivity.InfinityCategories.F2.Ind
