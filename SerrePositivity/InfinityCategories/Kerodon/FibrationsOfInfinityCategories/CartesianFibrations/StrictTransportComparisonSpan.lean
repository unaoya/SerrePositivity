module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftCoherentTransportReconstruction

/-! # strict transport の元の二脚と weighted 比較への因子分解を保持する復元 span

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.Fibration.StrictTransportComparisonSpan
end SerrePositivity.KST.Fibration.StrictTransportComparisonSpan
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.KST.Fibration

/-- 元の strict transport の共通全空間と二脚を、底の条件とともに保持する。 -/
structure StrictTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] where
  total : SSet.{u}
  projection : total ⟶ nerve I
  source : total ⟶ E
  weighted : total ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedNerve p
  inner : InnerFibration projection
  source_over : source ≫ p = projection
  weighted_over : weighted ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedProjection p = projection
  source_equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence source
  weighted_equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence weighted

/-- 構成済みの strict 復元 span を、元の二脚を保持するデータとして受け取る。 -/
theorem nonempty_strictTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan p) := by
  obtain ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_leftStrictTransport_reconstruction_span p
  exact ⟨⟨Z, t, a, b, ht, ha, hb, ea, eb⟩⟩

/-- 選択する対象に元の全空間・二脚・底上の条件をすべて含める。 -/
def strictTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan p :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.nonempty_strictTransportComparisonSpan p)

namespace StrictTransportComparisonSpan

variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan p)

/-- coherent な復元の元の共通底。 -/
def coherentBase : (SSet.uliftFunctor.{u + 1, u}).obj s.total ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) :=
  (SSet.uliftFunctor.{u + 1, u}).map s.projection

/-- coherent な復元でも、元の source 脚をそのまま持ち上げる。 -/
def coherentSource : (SSet.uliftFunctor.{u + 1, u}).obj s.total ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj E :=
  (SSet.uliftFunctor.{u + 1, u}).map s.source

/-- 元の weighted 脚と同じ既存比較を合成した、因子分解を保持する target 脚。 -/
def coherentTarget : (SSet.uliftFunctor.{u + 1, u}).obj s.total ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) :=
  (SSet.uliftFunctor.{u + 1, u}).map s.weighted ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransportComparison p

/-- 持ち上げた同じ source 脚は、元の共通底を厳密に保つ。 -/
theorem coherentSource_over :
    s.coherentSource ≫ (SSet.uliftFunctor.{u + 1, u}).map p = s.coherentBase := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan.coherentSource, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan.coherentBase, ← Functor.map_comp, s.source_over]

/-- 同じ weighted 比較を通る target 脚も、元の共通底を厳密に保つ。 -/
theorem coherentTarget_over :
    s.coherentTarget ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransport p) =
      s.coherentBase := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan.coherentTarget, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransportComparison_projection,
    ← Functor.map_comp, s.weighted_over]
  rfl

/-- 元の source 脚の同値性は、同じ宇宙持ち上げで保たれる。 -/
theorem coherentSource_equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence s.coherentSource := by
  have : InnerFibration s.projection := s.inner
  have : Quasicategory s.total := quasicategory_of_innerFibration s.projection
  have : Quasicategory E := quasicategory_of_innerFibration p
  exact s.source_equivalence.isQCatEquivalence.ulift.isPrecompositionEquivalence

/-- 元の weighted 脚と同じ比較の合成も前合成同値。 -/
theorem coherentTarget_equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence s.coherentTarget := by
  have : InnerFibration s.projection := s.inner
  have : Quasicategory s.total := quasicategory_of_innerFibration s.projection
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedNerve p) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedProjection p)
  exact s.weighted_equivalence.isQCatEquivalence.ulift.isPrecompositionEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftCoherentTransportComparison_isPrecompositionEquivalence p)

end StrictTransportComparisonSpan
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
