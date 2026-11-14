module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.RoofTargetFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible
/-!
概要：右 Kan 形状への実写像の Quillen A の slice を、同じ始域を持つ元の実屋根へ送る。
方針：slice の全錐を元の圏への射影で後合成し、二つの射影を pullback に持ち上げる。
規約：元の全高次錐を保ち、頂点の表示だけに還元しない。使われ方：実屋根比較による cofinality。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
variable {I X Q : SSet.{u}} (q : X ⟶ Q) (z : Q _⦋0⦌)
variable (f : I ⟶ X) (u : I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape q z)
variable (hu : u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection q z = f) (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape q z) _⦋0⦌)
/-- 右 Kan 比較の Quillen A で検査する、元の同じ実 slice の引き戻し。 -/
def rightKanCofinalSlice : SSet.{u} :=
  pullback u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))
/-- Quillen A の slice から元の添字への射影。 -/
def rightKanCofinalSliceProjection : rightKanCofinalSlice q z u b ⟶ I :=
  pullback.fst _ _
/-- Quillen A の実 slice の元の添字への射影は右ファイブレーション。 -/
instance rightKanCofinalSliceProjection_rightFibration
    [Quasicategory X] [Quasicategory Q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (rightKanCofinalSliceProjection q z u b) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_fst _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b)))⟩
/-- Quillen A の全 slice から元の実屋根への写像。 -/
def rightKanCofinalSliceRoofMap : rightKanCofinalSlice q z u b ⟶
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection q z).app (Opposite.op ⦋0⦌) b))) f :=
  pullback.lift (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection q z) b)
    (rightKanCofinalSliceProjection q z u b) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_projection, ← Category.assoc,
        ← pullback.condition, Category.assoc, hu]
      rfl)
/-- Quillen A の slice の実屋根表示は、元の同じ実添字を厳密に保持する。 -/
lemma rightKanCofinalSliceRoofMap_projection :
    rightKanCofinalSliceRoofMap q z f u hu b ≫ pullback.snd _ _ =
      rightKanCofinalSliceProjection q z u b :=
  pullback.lift_snd _ _ _
/-- Quillen A の slice の実屋根表示の分子は、元の全錐の射影そのもの。 -/
lemma rightKanCofinalSliceRoofMap_numerator :
    rightKanCofinalSliceRoofMap q z f u hu b ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection q z) b :=
  pullback.lift_fst _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
