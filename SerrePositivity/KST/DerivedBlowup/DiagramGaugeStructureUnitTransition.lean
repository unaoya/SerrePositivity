module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeStructureModule
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeUnit

/-!
概要：KST §3.1 の捻った構造加群の指定局所生成元の遷移を計算する。
方針：canonical な加群比較を単位矢の作用へ戻し、補助 representable で積を評価する。
規約：比較射自体の生成元への作用を示し、可逆な射の存在で代用しない。
使われ方：O(m) の regular 比較と canonical な係数拡大比較の可換式。
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

set_option maxHeartbeats 2000000 in
-- raw 制限と補助 representable の作用の対象を照合するために必要。
/-- 概要：捻り加群の指定遷移は局所単位生成元を重み付けした次の生成元へ送る。
方針：指定閉零係数射の gauge 像と包含単位の一般の左作用公式を使う。
規約：KST §3.1。使われ方：canonical な係数拡大比較の随伴像の計算。 -/
theorem diagramGaugeStructureLocalUnit_transition {i j : J} (h : i ≤ j) :
    diagramStructureLocalUnit F i ≫
        (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
          (diagramAlgebraModuleComparison F h (diagramGaugeStructureModule F s)) =
      MonObj.one (X := (F.obj j).X) ≫ (s.scale h).hom ≫
        diagramModuleHomInclusion (diagramAlgebraWithBottom F)
          (bot_le : (⊥ : WithBot J) ≤ (j : WithBot J)) := by
  rw [diagramAlgebraModuleComparison_eval, diagramModuleUnderlyingDiagram_map]
  change diagramStructureLocalUnit F i ≫ mapFromUnit R _ _
    (diagramModuleTransitionUnit F h ≫
      (diagramGaugeStructureRawModule F s).map (op (op ⟨i⟩)) (op (op ⟨j⟩))) = _
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  let M := diagramGaugeStructureRawModule F s
  let t : 𝟙_ (Complex R) ⟶
      (op (op (⟨i⟩ : DiagramModuleCoefficientObject F)) ⟶[Complex R] op (op ⟨j⟩)) :=
    diagramModuleTransitionUnit F h
  change (cycleFromUnit (M.obj (op (op ⟨j⟩)))
    (diagramStructureLocalUnit F i ≫ mapFromUnit R
      (M.obj (op (op ⟨i⟩))) (M.obj (op (op ⟨j⟩)))
      (t ≫ M.map (op (op ⟨i⟩)) (op (op ⟨j⟩))))).val = _
  rw [cycleFromUnit_postcomp]
  change (mapFromUnit R (M.obj (op (op ⟨i⟩))) (M.obj (op (op ⟨j⟩)))
    (t ≫ M.map (op (op ⟨i⟩)) (op (op ⟨j⟩)))).f 0
    (cycleFromUnit (M.obj (op (op ⟨i⟩))) (diagramStructureLocalUnit F i)).val = _
  rw [moduleClosedUnitAction_apply]
  change ((representableMap R
      (op (⟨⊥⟩ : DiagramModuleCoefficientObject (diagramAlgebraWithBottom F)))
      (op (op ⟨(i : WithBot J)⟩)) (op (op ⟨(j : WithBot J)⟩))).f 0
      (((diagramAlgebraBottomInclusion F).map ⟨i⟩ ⟨j⟩).f 0
        (((diagramGaugeDGFunctor F s).map ⟨i⟩ ⟨j⟩).f 0
          (cycleFromUnit _ (diagramModuleTransitionUnit F h)).val))).v 0 0 rfl
      (cycleFromUnit _ (diagramModuleTransitionUnit (diagramAlgebraWithBottom F)
        (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)))).val = _
  rw [diagramGaugeDGFunctor_bottom_unit_cycle, representableMap_apply, opposite_forward]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  exact diagramModuleTransitionUnit_forward_general (diagramAlgebraWithBottom F)
    (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)) (WithBot.coe_le_coe.mpr h) 0
    ((s.scale h).hom.f 0 (cycleFromUnit (F.obj j).X MonObj.one).val)

end SerrePositivity.KST.DerivedBlowup
