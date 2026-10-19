module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientModuleComponents

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数表示変更と canonical な局所加群比較。
方針：指定評価同型と局所制限四角形を挿入し、標準点の成分で単位矢の作用を比較する。
規約：構成済みの指定比較射を比較し、任意の局所同型へ置き換えない。
使われ方：主局所化上で cartesian 条件の表示不変性を証明する入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

set_option maxHeartbeats 2000000 in
-- 三段の局所制限と評価成分の対象同定に必要。
/-- 概要：canonical な局所加群比較は指定係数表示比較と可換。
方針：局所点で標準同型を恒等へ戻し、係数 dg 関手の単位矢保存を使う。
規約：KST §3.1・Lemma 3.6、全図式加群での指定射の等式。
使われ方：canonical な導来制限比較と随伴で移した係数拡大比較の表示変更。 -/
theorem diagramCoefficientModuleComparison_square {i j : J} (h : i ≤ j)
    (M : AllDiagramModules G) :
    diagramAlgebraModuleComparison F h ((diagramCoefficientRestriction α).obj M) ≫
      (moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
        (diagramAlgebraVertexTransition F h).op.op).map
          ((diagramCoefficientModuleEvaluationIso α j).hom.app M) ≫
      (diagramCoefficientModuleTransitionIso α h).hom.app
        ((diagramAlgebraModuleEvaluation G j).obj M) =
    (diagramCoefficientModuleEvaluationIso α i).hom.app M ≫
      (moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (G.obj i))ᵒᵖ
        (algebraVertexMap (α.app i)).op.op).map (diagramAlgebraModuleComparison G h M) := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  simp only [CategoryTheory.Functor.map_comp]
  rw [moduleRestriction_map_eval, moduleRestriction_map_eval,
    diagramCoefficientModuleEvaluationIso_hom_eval,
    diagramCoefficientModuleEvaluationIso_hom_eval,
    diagramCoefficientModuleTransitionIso_hom_eval,
    diagramAlgebraModuleComparison_eval, diagramAlgebraModuleComparison_eval]
  change (diagramModuleUnderlyingDiagram F
      (ForgetEnrichment.to (Complex R) ((diagramCoefficientRestriction α).obj M))).map
        (homOfLE h) ≫ 𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨j⟩))) ≫
        𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨j⟩))) =
    𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) ≫
      (diagramModuleUnderlyingDiagram G (ForgetEnrichment.to (Complex R) M)).map (homOfLE h)
  rw [Category.id_comp, Category.comp_id]
  exact (Category.comp_id _).trans (diagramCoefficientRestriction_underlying_map α h M)

end SerrePositivity.KST.DerivedBlowup
