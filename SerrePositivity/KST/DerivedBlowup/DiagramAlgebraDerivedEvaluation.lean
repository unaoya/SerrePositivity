module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraModuleComparison
public import SerrePositivity.DifferentialGraded.Derived.Restriction
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits

/-!
概要：KST §3.1 の正規表示の局所 dg 代数への主導来評価。
方針：指定埋め込みに沿う加群評価の擬同型保存で局所化へ降ろす。
規約：全図式の主導来圏を保持し、同じ局所代数の正規表示で評価する。
使われ方：正規表示の cartesian・perfect 条件と元の局所模型との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：正規表示への加群評価は全図式の擬同型を保つ。
方針：指定 dg 埋め込みに沿う加群制限の一般定理を使う。
規約：KST §3.1。使われ方：主局所化へ降ろすための入力。 -/
theorem diagramAlgebraModuleEvaluation_quasiIso (i : J) {M N : AllDiagramModules F}
    (f : M ⟶ N) (hf : moduleQuasiIso R (DiagramModuleCoefficientObject F)ᵒᵖ f) :
    moduleQuasiIso R (AlgebraVertex (F.obj i))ᵒᵖ
      ((diagramAlgebraModuleEvaluation F i).map f) :=
  moduleRestriction_quasiIso R _ _ _ f hf

/-- 概要：全図式の主導来圏から正規表示の局所導来加群圏への評価。
方針：指定 dg 埋め込みの opposite に沿う導来制限を使う。
規約：KST §3.1。使われ方：正規表示での局所 perfect 性と比較射。 -/
def diagramAlgebraDerivedEvaluation (i : J) :
    DerivedAllDiagramModules F ⥤ DerivedModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ :=
  dgDerivedRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramAlgebraVertexEmbedding F i).op

/-- 概要：主導来評価と実加群評価は主局所化を介して一致する。
方針：一般の導来制限の因子分解等式を適用する。
規約：KST §3.1。使われ方：正規表示での導来計算の指定経路。 -/
theorem diagramAlgebraDerivedEvaluation_fac (i : J) :
    moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ ⋙
        diagramAlgebraDerivedEvaluation F i =
      diagramAlgebraModuleEvaluation F i ⋙ moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ :=
  dgDerivedRestriction_fac R _ _ _

/-- 概要：正規表示の導来評価の標準計算自然同型。
方針：構成済みの因子分解等式を自然同型として読む。
規約：KST §3.1。使われ方：指定加群比較を導来自然変換へ移す。 -/
def diagramAlgebraDerivedEvaluationIso (i : J) :
    moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ ⋙
        diagramAlgebraDerivedEvaluation F i ≅
      diagramAlgebraModuleEvaluation F i ⋙ moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ :=
  eqToIso (diagramAlgebraDerivedEvaluation_fac F i)

/-- 概要：正規表示の局所加群評価の underlying 複体は元の当該添字の値。
方針：加群制限と評価の合成の一般公式を適用する。
規約：KST §3.1。使われ方：正規表示の評価が同じ局所切断を表すことの確認。 -/
theorem diagramAlgebraModuleEvaluation_comp_value (i : J) :
    diagramAlgebraModuleEvaluation F i ⋙
        moduleEvaluation R (AlgebraVertex (F.obj i))ᵒᵖ (op .point) =
      moduleEvaluation R (DiagramModuleCoefficientObject F)ᵒᵖ (op ⟨i⟩) :=
  moduleRestriction_comp_evaluation R _ _ _ _

end SerrePositivity.KST.DerivedBlowup
