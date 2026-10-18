module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeModuleComparisonSquare
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeDerivedRestrictionMate
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeDerivedEvaluation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation

/-!
概要：KST §3.1 の任意の導来図式加群の捻り比較を制限側 mate と同定する。
方針：実加群上の指定可換式を主局所化で送り、対象対応で全導来対象へ移す。
規約：指定局所同型・指定制限比較・局所化した mate の経路を保持する。
使われ方：canonical な導来係数拡大比較の可逆性を一般の対象へ移す。
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

/-- 概要：指定局所導来同型の実加群上の順射は通常局所同型の主局所化像。
方針：対象対応が実加群を回収することと等式移送の証明一意性を使う。
規約：KST §3.1。使われ方：指定比較の導来化を通常加群上で計算する。 -/
theorem diagramGaugeDerivedEvaluationIso_hom_Q (M : AllDiagramModules F) (i : J) :
    (diagramGaugeDerivedEvaluationIso F s
      ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M) i).hom =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        (diagramGaugeModuleLocalIso F s M i).hom := rfl

set_option maxHeartbeats 2000000 in
-- 局所導来評価と局所化前の指定加群比較の型を照合するために必要。
/-- 概要：任意の導来図式加群の捻り比較は局所同型を介して元の比較と mate に一致。
方針：全対象を主局所化の像へ戻し、指定通常加群比較の可換式を送る。
規約：KST §3.1。使われ方：指定随伴で canonical な係数拡大比較へ移す。 -/
theorem diagramGaugeDerivedComparison_square {i j : J} (h : i ≤ j)
    (X : DerivedAllDiagramModules F) :
    (diagramAlgebraDerivedRestrictionNatTrans F h).app ((diagramGaugeDerivedAction F s).obj X) ≫
        (diagramAlgebraDerivedRestriction F h).map (diagramGaugeDerivedEvaluationIso F s X j).hom =
      (diagramGaugeDerivedEvaluationIso F s X i).hom ≫
        (diagramAlgebraDerivedRestrictionNatTrans F h).app X ≫
        (diagramGaugeDerivedRestrictionIso F s h).hom.app
          ((diagramAlgebraDerivedEvaluation F j).obj X) := by
  obtain ⟨M, hM⟩ := (Localization.Construction.objEquiv
    (moduleQuasiIso R (DiagramModuleCoefficientObject F)ᵒᵖ)).surjective X
  change (moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M = X at hM
  subst X
  change (diagramAlgebraDerivedRestrictionNatTrans F h).app
      ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj
        ((diagramGaugeModuleAction F s).obj M)) ≫ _ = _
  rw [diagramAlgebraDerivedRestrictionNatTrans_app_Q_map,
    diagramGaugeDerivedEvaluationIso_hom_Q, diagramGaugeDerivedEvaluationIso_hom_Q,
    transitionDerivedRestriction_map_Q, diagramAlgebraDerivedRestrictionNatTrans_app_Q_map]
  change (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      (diagramAlgebraModuleComparison F h ((diagramGaugeModuleAction F s).obj M)) ≫
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        ((moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).map
          (diagramGaugeModuleLocalIso F s M j).hom) =
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        (diagramGaugeModuleLocalIso F s M i).hom ≫
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        (diagramAlgebraModuleComparison F h M) ≫
      (diagramGaugeDerivedRestrictionIso F s h).hom.app
        ((moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj
          ((diagramAlgebraModuleEvaluation F j).obj M))
  rw [diagramGaugeDerivedRestrictionIso_hom_app_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map)
      (diagramGaugeModuleComparison_square F s h M)

end SerrePositivity.KST.DerivedBlowup
