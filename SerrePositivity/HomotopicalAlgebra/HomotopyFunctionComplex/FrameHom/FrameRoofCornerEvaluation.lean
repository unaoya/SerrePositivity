module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerNormalization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofFiberPinched
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.TerminalFiberEvaluationWeak

/-!
# 元の実屋根 corner 全体から同じ次数の pinched Hom への弱評価

概要：元の全 corner を、指定次数の元の端点を持つ実写像空間へ送る。
方針：Over の恒等射上の fiber へ一つの全体評価を選び、その全底付き比較を保持する。
規約：元の点・元の q・全高次錐を保つ。Kan Hom 比較との照合は別工程。
使われ方：実 ProductCornerMap の弱同値性を元の写像空間の比較で検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q) _⦋0⦌)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)]

def roofCornerTerminalEvaluation : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTerminalEvaluation
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizedProjection A Y q b) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminal A Y q b) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizedProjection_leftFibration A Y q b
  exact Classical.choice (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofLeftFibration_terminalEvaluation_nonempty
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizedProjection A Y q b) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminal A Y q b)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminal_isTerminal A Y q b))

def roofCornerEvaluation :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (A.obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b))))
        (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizationMap A Y q b ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminalEvaluation A Y q b).evaluation ≫
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminalFiberIso A Y q b).hom ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetFiberPinchedIso A Y q (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b)).hom

lemma roofCornerEvaluation_weak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerEvaluation A Y q b) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizedProjection_leftFibration A Y q b
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (asIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizationMap A Y q b))).isWeakHomotopyEquivalence
  have h₁ := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.terminalFiberEvaluation_weak (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerNormalizedProjection A Y q b)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminal A Y q b) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminal_isTerminal A Y q b)
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminalEvaluation A Y q b)
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerTerminalFiberIso A Y q b)).isWeakHomotopyEquivalence
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetFiberPinchedIso A Y q (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetDegree A Y q b))).isWeakHomotopyEquivalence
  exact h₀.comp (h₁.comp (h₂.comp h₃))

lemma roofCornerEvaluation_weak_iff {S : SSet.{u}}
    (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCorner (SSet.yonedaEquiv.symm b) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (f ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerEvaluation A Y q b) :=
  ⟨fun h => h.comp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerEvaluation_weak A Y q b),
    fun h => (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerEvaluation_weak A Y q b).cancel_right h⟩

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
