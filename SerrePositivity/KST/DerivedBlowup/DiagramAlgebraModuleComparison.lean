module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex
public import SerrePositivity.KST.DerivedBlowup.TransitionModuleNaturality
public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence

/-!
概要：KST §3.1 の一対象正規表示に沿う図式加群の指定局所比較。
方針：指定単位矢の全次数自然変換を加群へ作用させ、標準制限合成同型を接続する。
規約：全 diagram-module は既存係数圏の opposite 上の右 dg 加群。
使われ方：対象移送を持たない局所表示での canonical な導来比較の入力。
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

/-- 概要：図式加群の正規化した局所 dg 代数での評価関手。
方針：局所埋め込みの二重 opposite に沿って加群を制限する。
規約：KST §3.1。使われ方：局所 perfect 性と cartesian 比較の行先。 -/
def diagramAlgebraModuleEvaluation (i : J) :
    AllDiagramModules F ⥤ ModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ :=
  moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    (diagramAlgebraVertexEmbedding F i).op.op

/-- 概要：局所遷移と埋め込みの合成に沿う一段の加群評価。
方針：指定 dg 関手の合成に沿って制限する。
規約：KST §3.1。使われ方：単位自然変換を作用させた直後の行先。 -/
def diagramAlgebraCompositeEvaluation {i j : J} (h : i ≤ j) :
    AllDiagramModules F ⥤ ModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ :=
  moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (DiagramModuleCoefficientObject F)ᵒᵖ
    ((diagramAlgebraVertexTransition F h).comp (diagramAlgebraVertexEmbedding F j)).op.op

/-- 概要：目標で評価してから正規表示の局所遷移で制限する二段の評価。
方針：実際の評価関手と局所制限を順に適用する。
規約：KST §3.1。使われ方：導来延長–制限随伴の制限側の行先。 -/
def diagramAlgebraIteratedEvaluation {i j : J} (h : i ≤ j) :
    AllDiagramModules F ⥤ ModuleCategory R (AlgebraVertex (F.obj i))ᵒᵖ :=
  diagramAlgebraModuleEvaluation F j ⋙
    moduleRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
      (diagramAlgebraVertexTransition F h).op.op

/-- 概要：一段と二段の局所加群評価の標準自然同型。
方針：既存の加群制限合成比較の逆を使う。
規約：KST §3.1。使われ方：指定局所比較の行先を二段の制限へ移す。 -/
def diagramAlgebraCompositeEvaluationIso {i j : J} (h : i ≤ j) :
    diagramAlgebraCompositeEvaluation F h ≅ diagramAlgebraIteratedEvaluation F h :=
  (moduleRestrictionCompIso R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (DiagramModuleCoefficientObject F)ᵒᵖ (diagramAlgebraVertexTransition F h).op.op
    (diagramAlgebraVertexEmbedding F j).op.op).symm

/-- 概要：指定単位矢による局所加群比較の自然変換。
方針：全次数自然変換の加群作用と標準制限合成同型を合成する。
規約：KST §3.1、任意同型の選択は含まない。
使われ方：全図式の主局所化上で canonical な比較を作る。 -/
def diagramAlgebraModuleComparisonNatTrans {i j : J} (h : i ≤ j) :
    diagramAlgebraModuleEvaluation F i ⟶ diagramAlgebraIteratedEvaluation F h :=
  transitionModuleNatTrans (diagramAlgebraVertexTransformation F h) ≫
    (diagramAlgebraCompositeEvaluationIso F h).hom

/-- 概要：各図式加群の指定局所比較射。
方針：構成済み自然変換の成分を取る。
規約：KST §3.1。使われ方：正規表示による cartesian 比較の加群レベルの入力。 -/
abbrev diagramAlgebraModuleComparison {i j : J} (h : i ≤ j) (M : AllDiagramModules F) :=
  (diagramAlgebraModuleComparisonNatTrans F h).app M

end SerrePositivity.KST.DerivedBlowup
