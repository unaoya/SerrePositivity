module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraDerivedSquare
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapAlgebraPerfectComparison
public import SerrePositivity.KST.DerivedBlowup.AdjointSquareComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramCartesianCondition

/-!
概要：KST §3.1 の canonical な cartesian 比較の局所 dg 表示不変性。
方針：表示の dg 準同値に沿う延長–制限同値と随伴四角形を使う。
規約：元の Koszul 模型の指定比較と正規表示の指定比較を比べる。
使われ方：正規表示での整合性を既存の大域 Perf 候補へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 4000000 in
-- 四つの指定 graph 随伴と局所 dg 表示の準同値を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の局所 dg 構造と正規表示を照合するために必要。
/-- 概要：元の Koszul 模型と正規表示の指定係数拡大比較の可逆性は一致する。
方針：指定制限比較の一致を延長–制限随伴の可換四角形へ送り、準同値の余単位を使う。
規約：KST §3.1。使われ方：二つの cartesian 条件の同定。 -/
theorem finiteOverlapAlgebraDerivedExtensionComparison_isIso_iff (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    IsIso (finiteOverlapDerivedExtensionComparison R a h X) ↔
      IsIso (diagramAlgebraDerivedExtensionComparison (finiteOverlapDGAlgebraDiagram R a) h X) := by
  let Γᵢ := (finiteOverlapAlgebraVertexToChart R a T).op
  let Γⱼ := (finiteOverlapAlgebraVertexToChart R a U).op
  have hΓᵢ := quasiEquivalence_op (finiteOverlapAlgebraVertexToChart R a T)
    (finiteOverlapAlgebraVertexToChart_quasiEquivalence R a T)
  have hΓⱼ := quasiEquivalence_op (finiteOverlapAlgebraVertexToChart R a U)
    (finiteOverlapAlgebraVertexToChart_quasiEquivalence R a U)
  let Aᵢ := dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a T)ᵒᵖ Γᵢ
  let Aⱼ := dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapAlgebraVertex R a U)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ Γⱼ
  let : IsIso (Aᵢ.counit.app ((finiteOverlapDerivedModuleEvaluation R a T).obj X)) :=
    dgDerivedExtensionCounit_isIso_all R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a T)ᵒᵖ Γᵢ hΓᵢ _
  let : IsIso (Aⱼ.counit.app ((finiteOverlapDerivedModuleEvaluation R a U).obj X)) :=
    dgDerivedExtensionCounit_isIso_all R (FiniteOverlapAlgebraVertex R a U)ᵒᵖ
      (FiniteOverlapVertexObject R a U)ᵒᵖ Γⱼ hΓⱼ _
  let : (dgDerivedExtension R (FiniteOverlapAlgebraVertex R a U)ᵒᵖ
      (FiniteOverlapVertexObject R a U)ᵒᵖ Γⱼ).IsEquivalence :=
    (dgFunctorDerivedEquivalence R (FiniteOverlapAlgebraVertex R a U)ᵒᵖ
      (FiniteOverlapVertexObject R a U)ᵒᵖ Γⱼ hΓⱼ).isEquivalence_functor
  apply adjointSquare_comparison_isIso_iff Aᵢ Aⱼ
    (dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapVertexObject R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op)
    (dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapAlgebraVertex R a U)ᵒᵖ
      (diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).op)
    (finiteOverlapAlgebraDerivedRestrictionSquare R a h)
    (finiteOverlapDerivedExtensionComparison R a h X)
    (diagramAlgebraDerivedExtensionComparison (finiteOverlapDGAlgebraDiagram R a) h X)
  rw [finiteOverlapDerivedExtensionComparison_adjunct]
  change (finiteOverlapAlgebraDerivedRestriction R a T).map
      (finiteOverlapDerivedRestrictionComparison R a h X) ≫
      (finiteOverlapAlgebraDerivedRestrictionSquare R a h).hom.app
        ((finiteOverlapDerivedModuleEvaluation R a U).obj X) =
    (dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapAlgebraVertex R a U)ᵒᵖ
      (diagramAlgebraVertexTransition (finiteOverlapDGAlgebraDiagram R a) h).op).homEquiv
        ((diagramAlgebraDerivedEvaluation (finiteOverlapDGAlgebraDiagram R a) T).obj X)
        ((diagramAlgebraDerivedEvaluation (finiteOverlapDGAlgebraDiagram R a) U).obj X)
        (diagramAlgebraDerivedExtensionComparison (finiteOverlapDGAlgebraDiagram R a) h X)
  rw [diagramAlgebraDerivedExtensionComparison_adjunct,
    finiteOverlapAlgebraDerivedRestrictionSquare_hom_app]
  change (finiteOverlapAlgebraDerivedRestriction R a T).map
      (finiteOverlapDerivedRestrictionComparison R a h X) ≫
      𝟙 ((finiteOverlapAlgebraDerivedRestriction R a T).obj
        ((finiteOverlapDerivedTransitionRestriction R a h).obj
          ((finiteOverlapDerivedModuleEvaluation R a U).obj X))) = _
  rw [Category.comp_id]
  exact finiteOverlapAlgebraDerivedRestrictionComparison R a h X

end SerrePositivity.KST.DerivedBlowup
