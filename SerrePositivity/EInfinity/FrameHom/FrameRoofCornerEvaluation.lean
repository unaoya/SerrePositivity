module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerNormalization
public import SerrePositivity.EInfinity.FrameHom.FrameRoofFiberPinched
public import SerrePositivity.EInfinity.FrameHom.TerminalFiberEvaluationWeak

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
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)
  [LeftFibration (roofTargetProjection A Y q)]

def roofCornerTerminalEvaluation : RoofTerminalEvaluation
    (roofCornerNormalizedProjection A Y q b) (roofCornerTerminal A Y q b) := by
  have := roofCornerNormalizedProjection_leftFibration A Y q b
  exact Classical.choice (roofLeftFibration_terminalEvaluation_nonempty
    (roofCornerNormalizedProjection A Y q b) (roofCornerTerminal A Y q b)
    (roofCornerTerminal_isTerminal A Y q b))

def roofCornerEvaluation :
    sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q) ⟶
      pinchedHom (q.app (op ⦋0⦌) (nerveVertex (A.obj (roofTargetDegree A Y q b))))
        (q.app (op ⦋0⦌) (nerveVertex Y)) :=
  roofCornerNormalizationMap A Y q b ≫ (roofCornerTerminalEvaluation A Y q b).evaluation ≫
    (roofCornerTerminalFiberIso A Y q b).hom ≫
      (roofTargetFiberPinchedIso A Y q (roofTargetDegree A Y q b)).hom

lemma roofCornerEvaluation_weak : IsWeakHomotopyEquivalence (roofCornerEvaluation A Y q b) := by
  have := roofCornerNormalizedProjection_leftFibration A Y q b
  have h₀ := (isPrecompositionEquivalence_of_iso
    (asIso (roofCornerNormalizationMap A Y q b))).isWeakHomotopyEquivalence
  have h₁ := terminalFiberEvaluation_weak (roofCornerNormalizedProjection A Y q b)
    (roofCornerTerminal A Y q b) (roofCornerTerminal_isTerminal A Y q b)
    (roofCornerTerminalEvaluation A Y q b)
  have h₂ := (isPrecompositionEquivalence_of_iso
    (roofCornerTerminalFiberIso A Y q b)).isWeakHomotopyEquivalence
  have h₃ := (isPrecompositionEquivalence_of_iso
    (roofTargetFiberPinchedIso A Y q (roofTargetDegree A Y q b))).isWeakHomotopyEquivalence
  exact h₀.comp (h₁.comp (h₂.comp h₃))

lemma roofCornerEvaluation_weak_iff {S : SSet.{u}}
    (f : S ⟶ sliceOverCorner (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q)) :
    IsWeakHomotopyEquivalence f ↔
      IsWeakHomotopyEquivalence (f ≫ roofCornerEvaluation A Y q b) :=
  ⟨fun h => h.comp (roofCornerEvaluation_weak A Y q b),
    fun h => (roofCornerEvaluation_weak A Y q b).cancel_right h⟩

end SerrePositivity.EInfinity.FrameHom.FrameArrows
