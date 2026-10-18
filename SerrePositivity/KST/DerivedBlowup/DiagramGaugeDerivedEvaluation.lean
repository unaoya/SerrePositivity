module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeLocal
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraLocallyPerfect

/-!
概要：KST §3.1 の gauge 制限は任意の導来図式加群の局所評価を保つ。
方針：raw 加群の局所制限同型を指定主局所化で送り、対象対応で全対象へ適用する。
規約：構造対象に限らず全対象の局所条件を扱う。cartesian 条件は別証明。
使われ方：一般の捻り作用による局所 perfect 性の保存と反映。
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

/-- 概要：指定 gauge に沿う全図式主導来圏の自己制限関手。
方針：構成済み dg 自己関手の opposite に沿う導来制限を使う。
規約：KST §3.1。使われ方：整数捻りの一般形。 -/
abbrev diagramGaugeDerivedAction :=
  dgDerivedRestriction R (DiagramModuleCoefficientObject F)ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramGaugeDGFunctor F s).op

/-- 概要：gauge 制限後の各局所導来評価は元の局所導来評価と同型。
方針：全対象を指定主局所化の像へ戻し、raw 局所制限同型を送る。
規約：KST §3.1。使われ方：一般の捻り対象の局所 perfect 性。 -/
def diagramGaugeDerivedEvaluationIso (X : DerivedAllDiagramModules F) (i : J) :
    (diagramAlgebraDerivedEvaluation F i).obj ((diagramGaugeDerivedAction F s).obj X) ≅
      (diagramAlgebraDerivedEvaluation F i).obj X := by
  let e := Localization.Construction.objEquiv
    (moduleQuasiIso R (DiagramModuleCoefficientObject F)ᵒᵖ)
  let M := e.symm X
  have hM : (moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj M = X :=
    e.apply_symm_apply X
  rw [← hM]
  exact (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).mapIso
    (diagramGaugeLocalIso F s (ForgetEnrichment.to (Complex R) M) i)

/-- 概要：gauge 制限は全図式導来対象の局所 perfect 性を保存・反映する。
方針：全局所評価の指定同型に沿って perfect 性を両方向に移す。
規約：KST §3.1、cartesian 性の保存は別義務。
使われ方：大域 Perf 候補への捻り作用の局所条件。 -/
theorem diagramGaugeDerivedAction_locallyPerfect_iff (X : DerivedAllDiagramModules F) :
    diagramAlgebraLocallyPerfect F ((diagramGaugeDerivedAction F s).obj X) ↔
      diagramAlgebraLocallyPerfect F X := by
  constructor
  · intro h i
    exact (modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ).prop_of_iso
      (diagramGaugeDerivedEvaluationIso F s X i) (h i)
  · intro h i
    exact (modulePerfect R (AlgebraVertex (F.obj i))ᵒᵖ).prop_of_iso
      (diagramGaugeDerivedEvaluationIso F s X i).symm (h i)

end SerrePositivity.KST.DerivedBlowup
