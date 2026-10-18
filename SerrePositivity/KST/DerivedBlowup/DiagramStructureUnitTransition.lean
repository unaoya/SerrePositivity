module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureRegularMap
public import SerrePositivity.KST.DerivedBlowup.ModuleClosedUnitEvaluation
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparisonComponents

/-!
概要：KST §3.1 の構造加群の局所単位生成元と指定遷移の整合性。
方針：補助係数圏への包含は指定単位を保ち、単位の cycle の合成は直接単位になる。
規約：canonical な比較射を生成元に作用させた等式として述べる。
使われ方：局所 regular 比較と構造加群の cartesian 比較の可換式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：補助係数圏への包含は元の指定包含単位を保つ。
方針：標準 Hom 同定の合成を移送の合成として計算する。
規約：KST §3.1。使われ方：構造加群の指定遷移を補助 representable で計算する。 -/
theorem diagramAlgebraBottomInclusion_unit {i j : J} (h : i ≤ j) :
    diagramModuleTransitionUnit F h ≫ (diagramAlgebraBottomInclusion F).map ⟨i⟩ ⟨j⟩ =
      diagramModuleTransitionUnit (diagramAlgebraWithBottom F) (WithBot.coe_le_coe.mpr h) := by
  change diagramModuleTransitionUnit F h ≫ eqToHom (diagramAlgebraWithBottom_hom F i j) = _
  simp only [diagramModuleTransitionUnit, Category.assoc, diagramModuleHomInclusion, eqToHom_trans]

/-- 概要：補助係数圏への包含は指定包含単位の閉零 cycle を保つ。
方針：複体上の単位保存を単位複体の生成元で評価する。
規約：KST §3.1。使われ方：representable の斉次作用の単位計算。 -/
theorem diagramAlgebraBottomInclusion_unit_cycle {i j : J} (h : i ≤ j) :
    ((diagramAlgebraBottomInclusion F).map ⟨i⟩ ⟨j⟩).f 0
      (cycleFromUnit _ (diagramModuleTransitionUnit F h)).val =
      (cycleFromUnit _ (diagramModuleTransitionUnit (diagramAlgebraWithBottom F)
        (WithBot.coe_le_coe.mpr h))).val := by
  have he := congrArg (fun f : 𝟙_ (Complex R) ⟶
      diagramModuleHom (diagramAlgebraWithBottom F) (i : WithBot J) (j : WithBot J) =>
      (cycleFromUnit _ f).val) (diagramAlgebraBottomInclusion_unit F h)
  rw [cycleFromUnit_postcomp] at he
  exact he

variable [Small.{u} (DiagramModuleCoefficientObject F)]

set_option maxHeartbeats 2000000 in
-- 元の係数圏からの制限と補助 representable の閉零作用を照合するために必要。
/-- 概要：構造加群の指定局所遷移は局所単位生成元を次の局所単位生成元へ送る。
方針：指定比較を単位矢の作用へ戻し、補助係数圏で単位 cycle の合成を計算する。
規約：KST §3.1。使われ方：canonical な cartesian 比較と regular 比較の整合性。 -/
theorem diagramStructureLocalUnit_transition {i j : J} (h : i ≤ j) :
    diagramStructureLocalUnit F i ≫
      (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
        (diagramAlgebraModuleComparison F h (diagramStructureModule F)) =
      diagramStructureLocalUnit F j := by
  rw [diagramAlgebraModuleComparison_eval, diagramModuleUnderlyingDiagram_map]
  change diagramStructureLocalUnit F i ≫ mapFromUnit R _ _
      (diagramModuleTransitionUnit F h ≫
        (diagramStructureRawModule F).map (op (op ⟨i⟩)) (op (op ⟨j⟩))) = _
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  let M := diagramStructureRawModule F
  let t : 𝟙_ (Complex R) ⟶
      (op (op (⟨i⟩ : DiagramModuleCoefficientObject F)) ⟶[Complex R] op (op ⟨j⟩)) :=
    diagramModuleTransitionUnit F h
  change (cycleFromUnit (M.obj (op (op ⟨j⟩)))
      (diagramStructureLocalUnit F i ≫ mapFromUnit R
        (M.obj (op (op ⟨i⟩))) (M.obj (op (op ⟨j⟩)))
        (t ≫ M.map (op (op ⟨i⟩)) (op (op ⟨j⟩))))).val =
    (cycleFromUnit (M.obj (op (op ⟨j⟩))) (diagramStructureLocalUnit F j)).val
  rw [cycleFromUnit_postcomp]
  change (mapFromUnit R (M.obj (op (op ⟨i⟩))) (M.obj (op (op ⟨j⟩)))
      (t ≫ M.map (op (op ⟨i⟩)) (op (op ⟨j⟩)))).f 0
      (cycleFromUnit (M.obj (op (op ⟨i⟩))) (diagramStructureLocalUnit F i)).val =
    (cycleFromUnit (M.obj (op (op ⟨j⟩))) (diagramStructureLocalUnit F j)).val
  rw [moduleClosedUnitAction_apply]
  change ((representableMap R
      (op (⟨⊥⟩ : DiagramModuleCoefficientObject (diagramAlgebraWithBottom F)))
      (op (op ⟨(i : WithBot J)⟩)) (op (op ⟨(j : WithBot J)⟩))).f 0
      (((diagramAlgebraBottomInclusion F).map ⟨i⟩ ⟨j⟩).f 0
        (cycleFromUnit _ (diagramModuleTransitionUnit F h)).val)).v 0 0 rfl
      (cycleFromUnit _ (diagramModuleTransitionUnit (diagramAlgebraWithBottom F)
        (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)))).val = _
  rw [diagramAlgebraBottomInclusion_unit_cycle, representableMap_apply, opposite_forward]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  exact diagramModuleTransitionUnit_forward_comp (diagramAlgebraWithBottom F)
    (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)) (WithBot.coe_le_coe.mpr h)

end SerrePositivity.KST.DerivedBlowup
