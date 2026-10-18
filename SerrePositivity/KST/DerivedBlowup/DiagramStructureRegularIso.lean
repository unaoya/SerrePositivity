module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureRegularMap
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects

/-!
概要：KST §3.1 の局所構造加群への直接 regular 比較は実際に同型。
方針：反復制限比較の恒等成分と補助 representable の Hom 同定を使う。
規約：擬同型性より強い局所の計算であり、大域の cartesian 性とは区別する。
使われ方：O(m) の局所 trivialization と canonical な遷移比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：直接 regular 比較の標準点成分は補助始点からの Hom の標準同定。
方針：指定制限比較の成分が恒等であることを使い、補助比較の評価へ戻す。
規約：KST §3.1。使われ方：局所同型の具体的な順成分。 -/
theorem diagramStructureLocalRegularMap_eval (i : J) :
    (moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map
      (diagramStructureLocalRegularMap F i) =
    diagramModuleHomInclusion (diagramAlgebraWithBottom F)
      (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)) := by
  have he := congrArg ((moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point)).map)
    (diagramStructureLocalRegularMap_comp F i)
  rw [CategoryTheory.Functor.map_comp, diagramStructureLocalComparisonIso_hom_eval,
    Category.comp_id] at he
  exact he.trans (diagramRepresentableLocalRegularMap_eval (diagramAlgebraWithBottom F)
    (bot_le : (⊥ : WithBot J) ≤ (i : WithBot J)))

/-- 概要：直接 regular 比較は局所加群圏の同型。
方針：標準点成分が標準 Hom 同定なので可逆であり、評価で同型を反映する。
規約：KST §3.1。使われ方：捻りの局所比較を通常加群の同型として扱う。 -/
theorem diagramStructureLocalRegularMap_isIso (i : J) :
    IsIso (diagramStructureLocalRegularMap F i) := by
  apply moduleIsIso_of_evaluations
  intro x
  have hx : x = op .point := by
    apply Opposite.unop_injective
    cases x.unop
    rfl
  subst x
  rw [diagramStructureLocalRegularMap_eval]
  unfold diagramModuleHomInclusion
  infer_instance

/-- 概要：直接 Yoneda 比較を順射に持つ局所 regular 同型。
方針：証明した可逆性を指定射の同型として束ねる。
規約：KST §3.1。使われ方：canonical な捻り比較の局所座標。 -/
def diagramStructureLocalRegularIso (i : J) :
    ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj i)))) ≅
      (diagramAlgebraModuleEvaluation F i).obj (diagramStructureModule F) := by
  letI := diagramStructureLocalRegularMap_isIso F i
  exact asIso (diagramStructureLocalRegularMap F i)

end SerrePositivity.KST.DerivedBlowup
