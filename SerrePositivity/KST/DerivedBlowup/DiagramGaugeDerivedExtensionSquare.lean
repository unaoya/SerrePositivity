module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeDerivedComparisonSquare
public import SerrePositivity.KST.DerivedBlowup.AdjointEndomorphismComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianCondition

/-!
概要：KST §3.1 の一般対象の捻りと canonical な係数拡大比較の可換式。
方針：指定随伴の Hom 同値で制限側の可換式へ戻し、同型の合成を消去する。
規約：canonical な比較射そのものの可逆性を保存・反映する。
使われ方：一般の cartesian perfect 対象への捻り作用。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)
variable [Small.{u} (DiagramModuleCoefficientObject F)]

set_option maxHeartbeats 2000000 in
-- 指定導来随伴と複数の局所比較の型を照合するために必要。
/-- 概要：捻りの canonical な係数拡大比較は局所同型と指定 mate を介して元の比較に一致。
方針：Hom 同値で移し、左自己同型の mate 公式と制限側可換式を使う。
規約：KST §3.1。使われ方：一般対象の cartesian 条件の保存と反映。 -/
theorem diagramGaugeDerivedExtensionComparison_square {i j : J} (h : i ≤ j)
    (X : DerivedAllDiagramModules F) :
    (diagramAlgebraDerivedExtension F h).map (diagramGaugeDerivedEvaluationIso F s X i).hom ≫
        (diagramGaugeDerivedExtensionMateIso F s h).hom.app
          ((diagramAlgebraDerivedEvaluation F i).obj X) ≫
        diagramAlgebraDerivedExtensionComparison F h X =
      diagramAlgebraDerivedExtensionComparison F h ((diagramGaugeDerivedAction F s).obj X) ≫
        (diagramGaugeDerivedEvaluationIso F s X j).hom := by
  let A := dgDerivedExtensionRestrictionAdjunction R
    (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, adjointEndomorphism_homEquiv A,
    A.homEquiv_naturality_right, diagramGaugeDerivedExtensionMateIso_conjugate,
    diagramAlgebraDerivedExtensionComparison_adjunct,
    diagramAlgebraDerivedExtensionComparison_adjunct]
  exact (diagramGaugeDerivedComparison_square F s h X).symm

/-- 概要：全包含で捻りの指定係数拡大比較の可逆性は元の比較の可逆性と同値。
方針：指定可換式の両側の局所同型と mate を消去する。
規約：KST §3.1。使われ方：cartesian 条件を全対象で両方向に移す。 -/
theorem diagramGaugeDerivedExtensionComparison_isIso_iff {i j : J} (h : i ≤ j)
    (X : DerivedAllDiagramModules F) :
    IsIso (diagramAlgebraDerivedExtensionComparison F h ((diagramGaugeDerivedAction F s).obj X)) ↔
      IsIso (diagramAlgebraDerivedExtensionComparison F h X) := by
  constructor
  · intro hTw
    let := hTw
    have hc : IsIso ((diagramAlgebraDerivedExtension F h).map
        (diagramGaugeDerivedEvaluationIso F s X i).hom ≫
        (diagramGaugeDerivedExtensionMateIso F s h).hom.app
          ((diagramAlgebraDerivedEvaluation F i).obj X) ≫
        diagramAlgebraDerivedExtensionComparison F h X) := by
      rw [diagramGaugeDerivedExtensionComparison_square]
      infer_instance
    let := hc
    have hm : IsIso ((diagramGaugeDerivedExtensionMateIso F s h).hom.app
        ((diagramAlgebraDerivedEvaluation F i).obj X) ≫
        diagramAlgebraDerivedExtensionComparison F h X) :=
      IsIso.of_isIso_comp_left
        ((diagramAlgebraDerivedExtension F h).map (diagramGaugeDerivedEvaluationIso F s X i).hom) _
    let := hm
    exact IsIso.of_isIso_comp_left
      ((diagramGaugeDerivedExtensionMateIso F s h).hom.app
        ((diagramAlgebraDerivedEvaluation F i).obj X)) _
  · intro hX
    let := hX
    have hc : IsIso (diagramAlgebraDerivedExtensionComparison F h
        ((diagramGaugeDerivedAction F s).obj X) ≫
        (diagramGaugeDerivedEvaluationIso F s X j).hom) := by
      rw [← diagramGaugeDerivedExtensionComparison_square]
      infer_instance
    let := hc
    exact IsIso.of_isIso_comp_right _ (diagramGaugeDerivedEvaluationIso F s X j).hom

/-- 概要：gauge 制限は任意の導来図式加群の cartesian 性を保存・反映する。
方針：全包含での canonical な比較の可逆性の同値を使う。
規約：KST §3.1。使われ方：大域 cartesian 部分圏への捻り作用。 -/
theorem diagramGaugeDerivedAction_cartesian_iff (X : DerivedAllDiagramModules F) :
    diagramAlgebraCartesian F ((diagramGaugeDerivedAction F s).obj X) ↔
      diagramAlgebraCartesian F X := by
  constructor
  · intro h i j g
    exact (diagramGaugeDerivedExtensionComparison_isIso_iff F s g X).mp (h i j g)
  · intro h i j g
    exact (diagramGaugeDerivedExtensionComparison_isIso_iff F s g X).mpr (h i j g)

/-- 概要：gauge 制限は任意の導来図式加群の cartesian perfect 性を保存・反映する。
方針：cartesian 比較と局所 perfect 条件の両方向の同値を合わせる。
規約：KST §3.1、層レベルの比較は別工程。
使われ方：大域 Perf 候補の全対象への捻り作用。 -/
theorem diagramGaugeDerivedAction_cartesianPerfect_iff (X : DerivedAllDiagramModules F) :
    diagramAlgebraCartesianPerfect F ((diagramGaugeDerivedAction F s).obj X) ↔
      diagramAlgebraCartesianPerfect F X :=
  and_congr (diagramGaugeDerivedAction_cartesian_iff F s X)
    (diagramGaugeDerivedAction_locallyPerfect_iff F s X)

end SerrePositivity.KST.DerivedBlowup
