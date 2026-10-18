module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeStructureUnitTransition
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeRegularIso
public import SerrePositivity.KST.DerivedBlowup.RepresentableUnitRecovery

/-!
概要：KST §3.1 の捻りの直接 regular 比較と指定加群遷移の可換式。
方針：生成元の遷移を Yoneda 拡張し、重み付けを局所 regular 自己同型へ分離する。
規約：canonical な比較射の等式として記述する。
使われ方：捻りの指定導来係数拡大比較を同型の合成に同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)
variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：重み付け生成元の Yoneda 射は regular 自己同型と直接比較の合成。
方針：代表加群の単位による回収公式と両射の標準点成分を使う。
規約：KST §3.1。使われ方：指定遷移の重みを可逆な加群射として扱う。 -/
theorem diagramGaugeStructureLocalRegularMap_weighted {i j : J} (h : i ≤ j) :
    representableUnitMap R (op (.point : AlgebraVertex (F.obj j)))
        (diagramGaugeStructureLocalRaw F s j)
        (MonObj.one (X := (F.obj j).X) ≫ (s.scale h).hom ≫
          diagramModuleHomInclusion (diagramAlgebraWithBottom F)
            (bot_le : (⊥ : WithBot J) ≤ (j : WithBot J))) =
      (diagramGaugeRegularIso F s h).hom ≫ diagramGaugeStructureLocalRegularMap F s j := by
  have he := representableUnitMap_recover R (op (.point : AlgebraVertex (F.obj j)))
    ((diagramGaugeRegularIso F s h).hom ≫ diagramGaugeStructureLocalRegularMap F s j)
  rw [CategoryTheory.Functor.map_comp, diagramGaugeRegularIso_hom_eval,
    diagramGaugeStructureLocalRegularMap_eval] at he
  exact he

/-- 概要：捻りの指定遷移は regular 比較を介して代表制限比較と重み自己同型に一致。
方針：Yoneda の後合成・制限自然性と生成元の遷移公式を合成する。
規約：KST §3.1。使われ方：指定係数拡大比較の随伴像の一致。 -/
theorem diagramGaugeStructureLocalRegularMap_transition {i j : J} (h : i ≤ j) :
    diagramGaugeStructureLocalRegularMap F s i ≫
        diagramAlgebraModuleComparison F h (diagramGaugeStructureModule F s) =
      representableRestrictionMap R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op (op .point) ≫
        (moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
          (diagramAlgebraVertexTransition F h).op.op).map
          ((diagramGaugeRegularIso F s h).hom ≫ diagramGaugeStructureLocalRegularMap F s j) := by
  change representableUnitMap R (op .point)
      (ForgetEnrichment.to (Complex R)
        ((diagramAlgebraModuleEvaluation F i).obj (diagramGaugeStructureModule F s)))
      (diagramStructureLocalUnit F i) ≫
        diagramAlgebraModuleComparison F h (diagramGaugeStructureModule F s) = _
  rw [representableUnitMap_postcomp, diagramGaugeStructureLocalUnit_transition]
  have he := representableUnitMap_restrict R (diagramAlgebraVertexTransition F h).op (op .point)
    (diagramGaugeStructureLocalRaw F s j)
    (MonObj.one (X := (F.obj j).X) ≫ (s.scale h).hom ≫
      diagramModuleHomInclusion (diagramAlgebraWithBottom F)
        (bot_le : (⊥ : WithBot J) ≤ (j : WithBot J)))
  rw [diagramGaugeStructureLocalRegularMap_weighted] at he
  exact he

end SerrePositivity.KST.DerivedBlowup
