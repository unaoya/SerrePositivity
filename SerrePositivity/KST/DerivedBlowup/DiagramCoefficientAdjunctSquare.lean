module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientDerivedComparisonSquare

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数表示変更と随伴像。
方針：canonical な制限比較の可換式を局所評価同型で共役する。
規約：任意の図式射について指定随伴での像を比較する。
使われ方：表示同型の場合の cartesian 比較の可逆性の保存・反映。
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
-- 二つの局所評価同型と指定随伴の対象を照合するために必要。
/-- 概要：指定評価同型で共役した係数拡大比較は元の制限比較の像を持つ。
方針：随伴の左右自然性で制限比較へ戻し、指定可換四角形から同型を消去する。
規約：KST §3.1・Lemma 3.6、図式加群模型による再構成。
使われ方：局所係数同値の随伴四角形の入力。 -/
theorem diagramCoefficientDerivedComparison_adjunct {i j : J} (h : i ≤ j)
    (X : DerivedAllDiagramModules G) :
    (diagramCoefficientLocalDerivedRestriction α i).map
        ((diagramAlgebraDerivedRestrictionNatTrans G h).app X) ≫
      (diagramCoefficientDerivedTransitionIso α h).inv.app
        ((diagramAlgebraDerivedEvaluation G j).obj X) =
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op).homEquiv _ _
      ((diagramAlgebraDerivedExtension F h).map
          ((diagramCoefficientDerivedEvaluationIso α i).inv.app X) ≫
        diagramAlgebraDerivedExtensionComparison F h
          ((diagramCoefficientDerivedRestrictionOf α).obj X) ≫
        (diagramCoefficientDerivedEvaluationIso α j).hom.app X) := by
  let A := dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  have ha : A.homEquiv
      ((diagramCoefficientDerivedRestrictionOf α ⋙ diagramAlgebraDerivedEvaluation F i).obj X)
      ((diagramAlgebraDerivedEvaluation F j).obj
        ((diagramCoefficientDerivedRestrictionOf α).obj X))
      (diagramAlgebraDerivedExtensionComparison F h
        ((diagramCoefficientDerivedRestrictionOf α).obj X)) =
    (diagramAlgebraDerivedRestrictionNatTrans F h).app
      ((diagramCoefficientDerivedRestrictionOf α).obj X) :=
    diagramAlgebraDerivedExtensionComparison_adjunct F h _
  rw [ha]
  apply (cancel_mono ((diagramCoefficientDerivedTransitionIso α h).hom.app
    ((diagramAlgebraDerivedEvaluation G j).obj X))).mp
  have he := congrArg
    (fun f => (diagramCoefficientDerivedEvaluationIso α i).inv.app X ≫ f)
    (diagramCoefficientDerivedComparison_square α h X)
  simp only [Iso.inv_hom_id_app_assoc] at he
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).trans he.symm

end SerrePositivity.KST.DerivedBlowup
