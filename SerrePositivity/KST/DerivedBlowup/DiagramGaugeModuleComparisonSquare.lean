module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeModuleComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeLocal

/-!
概要：KST §3.1 の一般対象の捻りに対する指定加群比較の可換式。
方針：指定局所同型で評価を同定し、包含の制限側 mate の作用公式を使う。
規約：指定比較射そのものの等式であり、同型の存在で代用しない。
使われ方：主導来圏へ送って canonical な係数拡大比較の可逆性を移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)
variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：任意図式加群の捻りの指定局所同型。
方針：raw 制限同型を通常加群圏の対象に適用する。
規約：KST §3.1。使われ方：指定加群比較の始域・終域を同定する。 -/
abbrev diagramGaugeModuleLocalIso (M : AllDiagramModules F) (i : J) :
    (diagramAlgebraModuleEvaluation F i).obj ((diagramGaugeModuleAction F s).obj M) ≅
      (diagramAlgebraModuleEvaluation F i).obj M :=
  diagramGaugeLocalIso F s (ForgetEnrichment.to (Complex R) M) i

/-- 概要：任意加群の指定局所 gauge 同型の標準点成分は恒等。
方針：raw 制限比較の評価公式で対象移送を計算する。
規約：KST §3.1。使われ方：指定加群比較の可換式を全次数で照合する。 -/
theorem diagramGaugeModuleLocalIso_hom_eval (M : AllDiagramModules F) (i : J) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      (diagramGaugeModuleLocalIso F s M i).hom = 𝟙 _ := by
  unfold diagramGaugeModuleLocalIso diagramGaugeLocalIso
  rw [rawTransitionRestrictionCompIso_hom_eval]
  rfl

set_option maxHeartbeats 2000000 in
-- 指定局所同型の制限後の成分と図式比較の型を照合するために必要。
/-- 概要：捻りの指定加群比較は局所同型を介して元の比較と制限側 mate に一致。
方針：標準点で評価し、恒等な局所同型成分と包含射の計算式を使う。
規約：KST §3.1。使われ方：canonical な係数拡大比較の導来化。 -/
theorem diagramGaugeModuleComparison_square {i j : J} (h : i ≤ j) (M : AllDiagramModules F) :
    diagramAlgebraModuleComparison F h ((diagramGaugeModuleAction F s).obj M) ≫
        (moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op.op).map
            (diagramGaugeModuleLocalIso F s M j).hom =
      (diagramGaugeModuleLocalIso F s M i).hom ≫ diagramAlgebraModuleComparison F h M ≫
        (diagramGaugeModuleRestrictionIso F s h).hom.app
          ((diagramAlgebraModuleEvaluation F j).obj M) := by
  apply moduleMorphism_ext
  intro x
  cases x using Opposite.rec
  rename_i x
  cases x
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, moduleRestriction_map_eval]
  change (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      (diagramAlgebraModuleComparison F h ((diagramGaugeModuleAction F s).obj M)) ≫
      (moduleEvaluation R (AlgebraVertex (F.obj j))ᵒᵖ (op .point)).map
        (diagramGaugeModuleLocalIso F s M j).hom =
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
        (diagramGaugeModuleLocalIso F s M i).hom ≫
      (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
        (diagramAlgebraModuleComparison F h M) ≫ _
  rw [diagramGaugeModuleLocalIso_hom_eval, diagramGaugeModuleLocalIso_hom_eval]
  rw [diagramAlgebraModuleComparison_eval, diagramAlgebraModuleComparison_eval]
  change (diagramModuleUnderlyingDiagram F
        (ForgetEnrichment.to (Complex R) ((diagramGaugeModuleAction F s).obj M))).map (homOfLE h) ≫
      𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨j⟩))) =
    𝟙 ((ForgetEnrichment.to (Complex R) M).obj (op (op ⟨i⟩))) ≫
      (diagramModuleUnderlyingDiagram F (ForgetEnrichment.to (Complex R) M)).map (homOfLE h) ≫
        (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
          ((diagramGaugeModuleRestrictionIso F s h).hom.app
            ((diagramAlgebraModuleEvaluation F j).obj M))
  exact (Category.comp_id _).trans
    ((diagramGaugeModuleUnderlying_map F s h M).trans (Category.id_comp _).symm)

end SerrePositivity.KST.DerivedBlowup
