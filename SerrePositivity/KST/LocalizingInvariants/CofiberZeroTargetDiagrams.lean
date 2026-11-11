module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberZeroTargetDiagrams

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPathSpace
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationComparisonProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberZeroSource

/-!
概要：零終点矢印の元の cofiber 全族を、同じ始点の suspension 全図式と比較する。
方針：元の二つの零角を保持して suspension 図式圏へ入れ、始点評価の fiber で比較する。
規約：比較は始点で恒等。使われ方：一般商の suspension 比較の二次の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (a.app (Opposite.op ⦋0⦌) x))

lemma zeroTargetDiagrams_source :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroTargetDiagrams X a ha ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0 =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have he := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.squares_bottom X a)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroTargetDiagrams, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  exact he

lemma zeroTargetDiagrams_target :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroTargetDiagrams X a ha ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroTargetDiagrams, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  rfl

lemma zeroTargetDiagrams_sameSource :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroTargetDiagrams X a ha ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0 =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.suspensionDiagramsAtSource X a ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0 := by
  rw [zeroTargetDiagrams_source, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.suspensionDiagramsAtSource_source]

def zeroTargetDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroTargetDiagrams X a ha)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.suspensionDiagramsAtSource X a) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramFamilyIso _ _ (zeroTargetDiagrams_sameSource X a ha)

lemma zeroTargetDiagramComparison_source_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (zeroTargetDiagramComparison X a ha)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).hom =
        Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.suspensionDiagramsAtSource X a ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)) :
            hoFunctor.obj ((ihom A).obj X))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorIsoOfTrivialKanFibration_projection_arrow _ _ _ (zeroTargetDiagrams_sameSource X a ha)

def zeroTargetRelativeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X a)
    ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.map X) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (zeroTargetDiagramComparison X a ha)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)
  rw [zeroTargetDiagrams_target] at e
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.suspensionDiagramsAtSource, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.SuspensionExactDiagrams.diagrams_target] using e

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
