module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalDerivedComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalModuleComparisonNaturality

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の指定導来比較射の自然性。
方針：加群比較の自然変換を標準計算同型で挟んで主局所化へ延長し、延長–制限随伴で移す。
規約：既存の対象ごとの指定射と成分が一致することも示す。
使われ方：cartesian 条件の同型不変性と導来降下の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：主局所化前の図式加群上での指定導来制限比較の自然変換。
方針：標準評価同型、加群比較の局所化、目標の標準計算同型の逆を合成する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：主局所化への自然変換の延長の入力。 -/
def finiteOverlapExceptionalDerivedRestrictionPreNatTrans (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    moduleToDerived R (DiagramModuleCoefficientObject (finiteOverlapExceptionalDGAlgebraDiagram
      R a))ᵒᵖ ⋙
        finiteOverlapExceptionalDerivedModuleEvaluation R a T ⟶
      moduleToDerived R (DiagramModuleCoefficientObject
        (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ ⋙
        finiteOverlapExceptionalDerivedModuleEvaluation R a U ⋙
          finiteOverlapExceptionalDerivedTransitionRestriction R a h :=
  (finiteOverlapExceptionalDerivedEvaluationIso R a T).hom ≫
    whiskerRight (finiteOverlapExceptionalModuleComparisonNatTrans R a h)
      (moduleToDerived R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ) ≫
    (finiteOverlapExceptionalDerivedRestrictedEvaluationIso R a h).inv

/-- 概要：局所化前の自然変換は指定した対象ごとの導来比較を成分に持つ。
方針：自然変換・標準同型の成分を展開する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：指定の経路を変更していないことの確認。 -/
theorem finiteOverlapExceptionalDerivedRestrictionPreNatTrans_app (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (finiteOverlapExceptionalDerivedRestrictionPreNatTrans R a h).app M =
      finiteOverlapExceptionalDerivedRestrictionComparisonOnModule R a h M := rfl

/-- 概要：主導来局所化上の指定局所制限比較の自然変換。
方針：構成済みの自然変換を局所化の自然変換延長で送る。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：cartesian 比較の随伴前の自然性。 -/
def finiteOverlapExceptionalDerivedRestrictionNatTrans (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapExceptionalDerivedModuleEvaluation R a T ⟶
      finiteOverlapExceptionalDerivedModuleEvaluation R a U ⋙
        finiteOverlapExceptionalDerivedTransitionRestriction R a h :=
  Localization.Construction.natTransExtension
    (W := moduleQuasiIso R (DiagramModuleCoefficientObject
      (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ)
    (finiteOverlapExceptionalDerivedRestrictionPreNatTrans R a h)

/-- 概要：導来自然変換の成分は既存の指定制限比較に一致する。
方針：主局所化の延長は対象の保持する加群で元の自然変換を評価する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：cartesian 条件で用いる指定射の自然性。 -/
theorem finiteOverlapExceptionalDerivedRestrictionNatTrans_app (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (finiteOverlapExceptionalDerivedRestrictionNatTrans R a h).app X =
      finiteOverlapExceptionalDerivedRestrictionComparison R a h X := rfl

/-- 概要：指定導来制限比較は導来図式加群の全ての射について自然。
方針：構成済み自然変換の自然性を取り出す。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：導来係数拡大比較の自然性。 -/
theorem finiteOverlapExceptionalDerivedRestrictionComparison_natural (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    {X Y : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)} (f : X ⟶ Y) :
    (finiteOverlapExceptionalDerivedModuleEvaluation R a T).map f ≫
        finiteOverlapExceptionalDerivedRestrictionComparison R a h Y =
      finiteOverlapExceptionalDerivedRestrictionComparison R a h X ≫
        (finiteOverlapExceptionalDerivedTransitionRestriction R a h).map
          ((finiteOverlapExceptionalDerivedModuleEvaluation R a U).map f) :=
  (finiteOverlapExceptionalDerivedRestrictionNatTrans R a h).naturality f

set_option maxHeartbeats 2000000 in
-- 局所化環の graph 随伴の型と評価の合成を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環の dg 模型と基底環上の構造を照合するために必要。
/-- 概要：指定導来係数拡大比較は導来図式加群の射について自然。
方針：構成済み随伴の Hom 同値の単射性と自然性で制限比較の自然性へ戻す。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：cartesian 条件の同型不変性。 -/
theorem finiteOverlapExceptionalDerivedExtensionComparison_natural (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    {X Y : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)} (f : X ⟶ Y) :
    (finiteOverlapExceptionalDerivedTransitionExtension R a h).map
        ((finiteOverlapExceptionalDerivedModuleEvaluation R a T).map f) ≫
        finiteOverlapExceptionalDerivedExtensionComparison R a h Y =
      finiteOverlapExceptionalDerivedExtensionComparison R a h X ≫
        (finiteOverlapExceptionalDerivedModuleEvaluation R a U).map f := by
  let A := dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
    (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ (finiteOverlapExceptionalLocalDGTransition R
      a h).op
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  rw [finiteOverlapExceptionalDerivedExtensionComparison_adjunct,
    finiteOverlapExceptionalDerivedExtensionComparison_adjunct]
  exact finiteOverlapExceptionalDerivedRestrictionComparison_natural R a h f

/-- 概要：導来係数拡大比較の実際の自然変換。
方針：指定の各比較射と証明済み自然性を束ねる。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：cartesian 部分圏の同型・三角構造の比較。 -/
def finiteOverlapExceptionalDerivedExtensionNatTrans
    (a : I → R) {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapExceptionalDerivedModuleEvaluation R a T ⋙
      finiteOverlapExceptionalDerivedTransitionExtension R a h ⟶
      finiteOverlapExceptionalDerivedModuleEvaluation R a U where
  app X := finiteOverlapExceptionalDerivedExtensionComparison R a h X
  naturality _ _ f := finiteOverlapExceptionalDerivedExtensionComparison_natural R a h f

end SerrePositivity.KST.DerivedBlowup
