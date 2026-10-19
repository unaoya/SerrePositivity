module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraDerivedSquare
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraPerfectComparison
public import SerrePositivity.KST.DerivedBlowup.AdjointSquareComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianCondition

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の canonical な cartesian 比較の局所 dg 表示不変性。
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
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：二つの cartesian 条件の同定。 -/
theorem finiteOverlapExceptionalAlgebraDerivedExtensionComparison_isIso_iff (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    IsIso (finiteOverlapExceptionalDerivedExtensionComparison R a h X) ↔
      IsIso (diagramAlgebraDerivedExtensionComparison (finiteOverlapExceptionalDGAlgebraDiagram
        R a) h X) := by
  let Γᵢ := (finiteOverlapExceptionalAlgebraVertexToChart R a T).op
  let Γⱼ := (finiteOverlapExceptionalAlgebraVertexToChart R a U).op
  have hΓᵢ := quasiEquivalence_op (finiteOverlapExceptionalAlgebraVertexToChart R a T)
    (finiteOverlapExceptionalAlgebraVertexToChart_quasiEquivalence R a T)
  have hΓⱼ := quasiEquivalence_op (finiteOverlapExceptionalAlgebraVertexToChart R a U)
    (finiteOverlapExceptionalAlgebraVertexToChart_quasiEquivalence R a U)
  let Aᵢ := dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapExceptionalAlgebraVertex R a
    T)ᵒᵖ
    (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ Γᵢ
  let Aⱼ := dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapExceptionalAlgebraVertex R a
    U)ᵒᵖ
    (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ Γⱼ
  let : IsIso (Aᵢ.counit.app ((finiteOverlapExceptionalDerivedModuleEvaluation R a T).obj X)) :=
    dgDerivedExtensionCounit_isIso_all R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ Γᵢ hΓᵢ _
  let : IsIso (Aⱼ.counit.app ((finiteOverlapExceptionalDerivedModuleEvaluation R a U).obj X)) :=
    dgDerivedExtensionCounit_isIso_all R (FiniteOverlapExceptionalAlgebraVertex R a U)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ Γⱼ hΓⱼ _
  let : (dgDerivedExtension R (FiniteOverlapExceptionalAlgebraVertex R a U)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ Γⱼ).IsEquivalence :=
    (dgFunctorDerivedEquivalence R (FiniteOverlapExceptionalAlgebraVertex R a U)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ Γⱼ hΓⱼ).isEquivalence_functor
  apply adjointSquare_comparison_isIso_iff Aᵢ Aⱼ
    (dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ (finiteOverlapExceptionalLocalDGTransition
        R a h).op)
    (dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapExceptionalAlgebraVertex R a U)ᵒᵖ
      (diagramAlgebraVertexTransition (finiteOverlapExceptionalDGAlgebraDiagram R a) h).op)
    (finiteOverlapExceptionalAlgebraDerivedRestrictionSquare R a h)
    (finiteOverlapExceptionalDerivedExtensionComparison R a h X)
    (diagramAlgebraDerivedExtensionComparison (finiteOverlapExceptionalDGAlgebraDiagram R a) h X)
  rw [finiteOverlapExceptionalDerivedExtensionComparison_adjunct]
  change (finiteOverlapExceptionalAlgebraDerivedRestriction R a T).map
      (finiteOverlapExceptionalDerivedRestrictionComparison R a h X) ≫
      (finiteOverlapExceptionalAlgebraDerivedRestrictionSquare R a h).hom.app
        ((finiteOverlapExceptionalDerivedModuleEvaluation R a U).obj X) =
    (dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapExceptionalAlgebraVertex R a T)ᵒᵖ
      (FiniteOverlapExceptionalAlgebraVertex R a U)ᵒᵖ
      (diagramAlgebraVertexTransition (finiteOverlapExceptionalDGAlgebraDiagram R a)
        h).op).homEquiv
        ((diagramAlgebraDerivedEvaluation (finiteOverlapExceptionalDGAlgebraDiagram R a) T).obj X)
        ((diagramAlgebraDerivedEvaluation (finiteOverlapExceptionalDGAlgebraDiagram R a) U).obj X)
        (diagramAlgebraDerivedExtensionComparison (finiteOverlapExceptionalDGAlgebraDiagram R a)
          h X)
  rw [diagramAlgebraDerivedExtensionComparison_adjunct,
    finiteOverlapExceptionalAlgebraDerivedRestrictionSquare_hom_app]
  change (finiteOverlapExceptionalAlgebraDerivedRestriction R a T).map
      (finiteOverlapExceptionalDerivedRestrictionComparison R a h X) ≫
      𝟙 ((finiteOverlapExceptionalAlgebraDerivedRestriction R a T).obj
        ((finiteOverlapExceptionalDerivedTransitionRestriction R a h).obj
          ((finiteOverlapExceptionalDerivedModuleEvaluation R a U).obj X))) = _
  rw [Category.comp_id]
  exact finiteOverlapExceptionalAlgebraDerivedRestrictionComparison R a h X

end SerrePositivity.KST.DerivedBlowup
