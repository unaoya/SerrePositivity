module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSliceComparisonEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：充満忠実関手による左 Kan 添字の全空間比較。
方針：元の slice 比較を同じ底へ引き戻し、実引き戻しの結合と交換で左 Kan 添字へ戻す。
規約：元の全図式と指定頂点を保持する。
使われ方：compact 全部分模型からの Ind 密度余錐の移送。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
  (δ : K ⟶ C) (f : C ⟶ D) (z : C _⦋0⦌)

/-- 概要：元の指定頂点の slice 射影。
方針：元の slice の公開射影を使う。
規約：元の指定頂点を保持する。
使われ方：全左 Kan 添字の底変換比較。 -/
abbrev leftKanAmbientSourceProjection := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)
/-- 概要：像の slice を元の圏へ戻した射影。
方針：元の slice の公開射影を使う。
規約：元の指定頂点を保持する。
使われ方：全左 Kan 添字の底変換比較。 -/
abbrev leftKanAmbientTargetProjection := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePullbackProjection f z
/-- 概要：像の指定頂点の slice 射影。
方針：元の slice の公開射影を使う。
規約：元の指定頂点を保持する。
使われ方：全左 Kan 添字の底変換比較。 -/
abbrev leftKanAmbientImageProjection :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) z))

/-- 概要：元の slice 比較の指定図式への底変換。
方針：同じ底上の比較を引き戻す。
規約：元の始域射影を保つ。
使われ方：左 Kan 全添字比較の中間射。 -/
def leftKanAmbientRestrictedComparison :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange (leftKanAmbientSourceProjection z) (leftKanAmbientTargetProjection f z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison f z) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison_projection f z) δ

private lemma leftKanAmbientRestrictedComparison_isQCatEquivalence (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (leftKanAmbientRestrictedComparison δ f z) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pullback.snd (leftKanAmbientSourceProjection z) δ) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pullback.snd (leftKanAmbientTargetProjection f z) δ) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩
  have : Quasicategory (pullback (leftKanAmbientSourceProjection z) δ) :=
    quasicategory_of_innerFibration (pullback.snd (leftKanAmbientSourceProjection z) δ)
  have : Quasicategory (pullback (leftKanAmbientTargetProjection f z) δ) :=
    quasicategory_of_innerFibration (pullback.snd (leftKanAmbientTargetProjection f z) δ)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isQCatEquivalence_of_rightFibration_fibers
    (pullback.snd (leftKanAmbientSourceProjection z) δ) (pullback.snd (leftKanAmbientTargetProjection f z) δ)
    (leftKanAmbientRestrictedComparison δ f z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection _ _ _ _ _)
  intro k
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso (leftKanAmbientSourceProjection z) δ k)).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison_fiber_isQCatEquivalence f hf z (δ.app (Opposite.op ⦋0⦌) k))
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_fiber (leftKanAmbientSourceProjection z) (leftKanAmbientTargetProjection f z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison f z) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSliceComparison_projection f z) δ k
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso (leftKanAmbientTargetProjection f z) δ k)).isQCatEquivalence.cancel_right
    ((congrArg (fun g ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g) hcomp).mpr he)

/-- 概要：充満忠実関手による左 Kan 添字の元の全比較射。
方針：slice 比較の底変換と引き戻しの結合・交換を合成する。
規約：始域 K の射影を保持する。
使われ方：同値による全密度余錐の移送。 -/
def leftKanAmbientComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ z ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (δ ≫ f) (f.app (Opposite.op ⦋0⦌) z) :=
  (pullbackSymmetry δ (leftKanAmbientSourceProjection z)).hom ≫ leftKanAmbientRestrictedComparison δ f z ≫
    (pullbackLeftPullbackSndIso (leftKanAmbientImageProjection f z) f δ).hom ≫
    (pullbackSymmetry (leftKanAmbientImageProjection f z) (δ ≫ f)).hom

/-- 概要：充満忠実関手による同じ左 Kan 全添字比較は全同値。
方針：元の全 slice 比較の各 fiber の同値を同じ底へ移す。
規約：元の関手に inner fibration 性は要求しない。
使われ方：Ind と元の圏の標準余錐の余極限性の比較。 -/
lemma leftKanAmbientComparison_isQCatEquivalence (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (leftKanAmbientComparison δ f z) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pullback.snd (leftKanAmbientSourceProjection z) δ) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pullback.snd (leftKanAmbientTargetProjection f z) δ) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (pullback.snd (leftKanAmbientImageProjection f z) (δ ≫ f)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_snd _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩
  have : Quasicategory (pullback (leftKanAmbientSourceProjection z) δ) :=
    quasicategory_of_innerFibration (pullback.snd (leftKanAmbientSourceProjection z) δ)
  have : Quasicategory (pullback (leftKanAmbientTargetProjection f z) δ) :=
    quasicategory_of_innerFibration (pullback.snd (leftKanAmbientTargetProjection f z) δ)
  have : Quasicategory (pullback (leftKanAmbientImageProjection f z) (δ ≫ f)) :=
    quasicategory_of_innerFibration (pullback.snd (leftKanAmbientImageProjection f z) (δ ≫ f))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pullbackSymmetry δ (leftKanAmbientSourceProjection z))).isQCatEquivalence.comp
    ((leftKanAmbientRestrictedComparison_isQCatEquivalence δ f z hf).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pullbackLeftPullbackSndIso (leftKanAmbientImageProjection f z) f δ)).isQCatEquivalence.comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pullbackSymmetry (leftKanAmbientImageProjection f z) (δ ≫ f))).isQCatEquivalence))

/-- 概要：全左 Kan 添字比較は元の始域射影を保つ。
方針：引き戻しの結合・交換と底変換の各射影公式を使う。
規約：全射の厳密な等式。
使われ方：密度図式そのものの比較。 -/
lemma leftKanAmbientComparison_projection :
    leftKanAmbientComparison δ f z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (δ ≫ f) (f.app _ z) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ z := by
  dsimp only [leftKanAmbientComparison, leftKanAmbientRestrictedComparison,
    leftKanAmbientTargetProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePullbackProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackLeftPullbackSndIso_hom_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange, pullback.lift_snd,
    pullbackSymmetry_hom_comp_snd]


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
