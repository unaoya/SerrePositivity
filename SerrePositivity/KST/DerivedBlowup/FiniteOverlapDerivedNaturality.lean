module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDerivedComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleComparisonNaturality

/-!
概要：KST §3.1 の指定導来比較射の自然性。
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
規約：KST §3.1。使われ方：主局所化への自然変換の延長の入力。 -/
def finiteOverlapDerivedRestrictionPreNatTrans (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ ⋙
        finiteOverlapDerivedModuleEvaluation R a T ⟶
      moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ ⋙
        finiteOverlapDerivedModuleEvaluation R a U ⋙
          finiteOverlapDerivedTransitionRestriction R a h :=
  (finiteOverlapDerivedEvaluationIso R a T).hom ≫
    whiskerRight (finiteOverlapModuleComparisonNatTrans R a h)
      (moduleToDerived R (FiniteOverlapVertexObject R a T)ᵒᵖ) ≫
    (finiteOverlapDerivedRestrictedEvaluationIso R a h).inv

/-- 概要：局所化前の自然変換は指定した対象ごとの導来比較を成分に持つ。
方針：自然変換・標準同型の成分を展開する。
規約：KST §3.1。使われ方：指定の経路を変更していないことの確認。 -/
theorem finiteOverlapDerivedRestrictionPreNatTrans_app (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedRestrictionPreNatTrans R a h).app M =
      finiteOverlapDerivedRestrictionComparisonOnModule R a h M := rfl

/-- 概要：主導来局所化上の指定局所制限比較の自然変換。
方針：構成済みの自然変換を局所化の自然変換延長で送る。
規約：KST §3.1。使われ方：cartesian 比較の随伴前の自然性。 -/
def finiteOverlapDerivedRestrictionNatTrans (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapDerivedModuleEvaluation R a T ⟶
      finiteOverlapDerivedModuleEvaluation R a U ⋙
        finiteOverlapDerivedTransitionRestriction R a h :=
  Localization.Construction.natTransExtension
    (W := moduleQuasiIso R (BlowupDiagramCoefficientObject R a)ᵒᵖ)
    (finiteOverlapDerivedRestrictionPreNatTrans R a h)

/-- 概要：導来自然変換の成分は既存の指定制限比較に一致する。
方針：主局所化の延長は対象の保持する加群で元の自然変換を評価する。
規約：KST §3.1。使われ方：cartesian 条件で用いる指定射の自然性。 -/
theorem finiteOverlapDerivedRestrictionNatTrans_app (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedRestrictionNatTrans R a h).app X =
      finiteOverlapDerivedRestrictionComparison R a h X := rfl

/-- 概要：指定導来制限比較は導来図式加群の全ての射について自然。
方針：構成済み自然変換の自然性を取り出す。
規約：KST §3.1。使われ方：導来係数拡大比較の自然性。 -/
theorem finiteOverlapDerivedRestrictionComparison_natural (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    {X Y : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)} (f : X ⟶ Y) :
    (finiteOverlapDerivedModuleEvaluation R a T).map f ≫
        finiteOverlapDerivedRestrictionComparison R a h Y =
      finiteOverlapDerivedRestrictionComparison R a h X ≫
        (finiteOverlapDerivedTransitionRestriction R a h).map
          ((finiteOverlapDerivedModuleEvaluation R a U).map f) :=
  (finiteOverlapDerivedRestrictionNatTrans R a h).naturality f

set_option maxHeartbeats 2000000 in
-- 局所化環の graph 随伴の型と評価の合成を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環の dg 模型と基底環上の構造を照合するために必要。
/-- 概要：指定導来係数拡大比較は導来図式加群の射について自然。
方針：構成済み随伴の Hom 同値の単射性と自然性で制限比較の自然性へ戻す。
規約：KST §3.1。使われ方：cartesian 条件の同型不変性。 -/
theorem finiteOverlapDerivedExtensionComparison_natural (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    {X Y : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)} (f : X ⟶ Y) :
    (finiteOverlapDerivedTransitionExtension R a h).map
        ((finiteOverlapDerivedModuleEvaluation R a T).map f) ≫
        finiteOverlapDerivedExtensionComparison R a h Y =
      finiteOverlapDerivedExtensionComparison R a h X ≫
        (finiteOverlapDerivedModuleEvaluation R a U).map f := by
  let A := dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  rw [finiteOverlapDerivedExtensionComparison_adjunct,
    finiteOverlapDerivedExtensionComparison_adjunct]
  exact finiteOverlapDerivedRestrictionComparison_natural R a h f

/-- 概要：導来係数拡大比較の実際の自然変換。
方針：指定の各比較射と証明済み自然性を束ねる。
規約：KST §3.1。使われ方：cartesian 部分圏の同型・三角構造の比較。 -/
def finiteOverlapDerivedExtensionNatTrans (a : I → R) {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapDerivedModuleEvaluation R a T ⋙ finiteOverlapDerivedTransitionExtension R a h ⟶
      finiteOverlapDerivedModuleEvaluation R a U where
  app X := finiteOverlapDerivedExtensionComparison R a h X
  naturality _ _ f := finiteOverlapDerivedExtensionComparison_natural R a h f

end SerrePositivity.KST.DerivedBlowup
