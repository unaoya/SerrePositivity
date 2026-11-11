module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomIdentityAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison

/-!
概要：実際の Hom 大域比較の各 fiber の同値性を、同じ恒等射の作用から証明する。
方針：恒等係数への合成作用の標準同型と pointed fiber 比較を合成し、標準 Hom 比較を消去する。
規約：構成済みの同じ大域比較の fiber 射を使用する。
使われ方：表現可能 coslice と Hom 関手の unstraightening の大域同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 全 Hom の恒等射係数への作用は、実際の反転した一点関手空間への同型。 -/
lemma relativeHomIdentityAction_isIso {B : SSet.{u}} (q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityAction q r) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityAction_eq]
  infer_instance

/-- 元の一つの大域比較の実際の pointed fiber 射は、各対象で同値。 -/
lemma relativeHomCosliceComparisonFiber_isQCatEquivalence {B : SSet.{u}}
    (q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparisonFiber q r) := by
  have := relativeHomIdentityAction_isIso q r
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityAction q r))).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison_isQCatEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj r))
  have h₁ := h₀.ofFunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparisonFiber_identityActionIso q r).symm
  have hk := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom q r)).symm).isQCatEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison_homotopyEquivalence q r).isQCatEquivalence
  exact hk.cancel_left h₁

/-- 元の大域比較の native な fiber 射も、既存の同じ fiber 同型を消去して同値。 -/
lemma relativeHomCosliceComparison_nativeFiber_isQCatEquivalence {B : SSet.{u}}
    (q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparison q)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparison_projection q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex r)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomUnstraighteningFiberIso q r)).isQCatEquivalence.cancel_right
    (relativeHomCosliceComparisonFiber_isQCatEquivalence q r)

/-- 恒等点から構成した一つの coslice 比較は、全空間の実際の同値。 -/
lemma relativeHomCosliceComparison_isQCatEquivalence {B : SSet.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparison q) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex q)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation q.val))
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparison q) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparison_projection q)
  intro s
  obtain ⟨r, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)).surjective s
  exact relativeHomCosliceComparison_nativeFiber_isQCatEquivalence q r

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
