module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientModuleComparisonSquare
public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComputation

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数変更と canonical な導来比較。
方針：指定通常加群比較の可換式を主局所化へ送り、全導来対象へ移す。
規約：指定局所評価同型・遷移同型の経路を保持する図式加群での再構成。
使われ方：表示同値による cartesian 条件の保存・反映。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

set_option maxHeartbeats 2000000 in
-- 全体と局所の主局所化および反復制限の対象同定に必要。
/-- 概要：係数変更後の canonical な導来制限比較は指定局所同型と可換。
方針：全対象を主局所化の像へ戻し、通常加群の可換式を局所化する。
規約：KST §3.1・Lemma 3.6、通常加群模型による再構成。
使われ方：随伴の四角形を用いた係数拡大比較の可逆性の比較。 -/
theorem diagramCoefficientDerivedComparison_square {i j : J} (h : i ≤ j)
    (X : DerivedAllDiagramModules G) :
    (diagramAlgebraDerivedRestrictionNatTrans F h).app
        ((diagramCoefficientDerivedRestrictionOf α).obj X) ≫
      (diagramAlgebraDerivedRestriction F h).map
        ((diagramCoefficientDerivedEvaluationIso α j).hom.app X) ≫
      (diagramCoefficientDerivedTransitionIso α h).hom.app
        ((diagramAlgebraDerivedEvaluation G j).obj X) =
    (diagramCoefficientDerivedEvaluationIso α i).hom.app X ≫
      (diagramCoefficientLocalDerivedRestriction α i).map
        ((diagramAlgebraDerivedRestrictionNatTrans G h).app X) := by
  obtain ⟨M, hM⟩ := (Localization.Construction.objEquiv
    (moduleQuasiIso R (DiagramModuleCoefficientObject G)ᵒᵖ)).surjective X
  change (moduleToDerived R (DiagramModuleCoefficientObject G)ᵒᵖ).obj M = X at hM
  subst X
  change (diagramAlgebraDerivedRestrictionNatTrans F h).app
    ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj
      ((diagramCoefficientRestriction α).obj M)) ≫ _ = _
  rw [diagramAlgebraDerivedRestrictionNatTrans_app_Q_map,
    diagramCoefficientDerivedEvaluationIso_hom_app_Q,
    diagramCoefficientDerivedEvaluationIso_hom_app_Q,
    transitionDerivedRestriction_map_Q, diagramAlgebraDerivedRestrictionNatTrans_app_Q_map,
    transitionDerivedRestriction_map_Q]
  change (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      (diagramAlgebraModuleComparison F h ((diagramCoefficientRestriction α).obj M)) ≫
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      ((moduleRestriction R _ _ (diagramAlgebraVertexTransition F h).op.op).map
        ((diagramCoefficientModuleEvaluationIso α j).hom.app M)) ≫
    (diagramCoefficientDerivedTransitionIso α h).hom.app
      ((moduleToDerived R (AlgebraVertex (G.obj j))ᵒᵖ).obj
        ((diagramAlgebraModuleEvaluation G j).obj M)) =
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      ((diagramCoefficientModuleEvaluationIso α i).hom.app M) ≫
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      ((moduleRestriction R _ _ (algebraVertexMap (α.app i)).op.op).map
        (diagramAlgebraModuleComparison G h M))
  rw [diagramCoefficientDerivedTransitionIso_hom_app_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map)
      (diagramCoefficientModuleComparison_square α h M)

end SerrePositivity.KST.DerivedBlowup
