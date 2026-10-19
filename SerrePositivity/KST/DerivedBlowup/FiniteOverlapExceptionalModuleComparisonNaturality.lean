module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalModuleComparison
public import SerrePositivity.KST.DerivedBlowup.TransitionModuleNaturality

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の指定局所加群比較を実際の自然変換に束ねる。
方針：指定 GradedNatTrans の加群作用の自然性と標準制限合成同型を合成する。
規約：各対象上の射は構成済みの canonical な比較射と一致する。
使われ方：主導来局所化への自然変換の延長。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 局所化環の単位自然変換と加群制限関手の型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環と共通基底環の構造を照合するために必要。
/-- 概要：合成埋め込みへの指定局所加群比較の自然変換。
方針：構成済み全次数自然変換の加群作用をそのまま適用する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：二段の制限への自然な比較の前半。 -/
def finiteOverlapExceptionalModuleComparisonToCompositeNatTrans (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapExceptionalModuleEvaluation R a T ⟶
      finiteOverlapExceptionalCompositeModuleEvaluation R a h :=
  transitionModuleNatTrans (finiteOverlapExceptionalTransitionGradedNatTrans R a h)

/-- 概要：反復した局所制限への canonical な加群比較の自然変換。
方針：指定単位矢の作用と標準制限合成同型の自然性を合成する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：導来局所制限比較の自然変換。 -/
def finiteOverlapExceptionalModuleComparisonNatTrans
    (a : I → R) {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    finiteOverlapExceptionalModuleEvaluation R a T ⟶
      finiteOverlapExceptionalIteratedModuleEvaluation R a h :=
  finiteOverlapExceptionalModuleComparisonToCompositeNatTrans R a h ≫
    (finiteOverlapExceptionalCompositeEvaluationIso R a h).hom

/-- 概要：構成した自然変換の成分は元の指定比較射に一致する。
方針：自然変換の合成を対象で評価する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：導来比較で使う経路の同一性。 -/
theorem finiteOverlapExceptionalModuleComparisonNatTrans_app (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (finiteOverlapExceptionalModuleComparisonNatTrans R a h).app M =
      finiteOverlapExceptionalModuleComparison R a h M := rfl

/-- 概要：指定の局所加群比較は入力図式加群の射について自然。
方針：構成済みの自然変換の自然性を取り出す。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：objectwise 擬同型での比較と導来自然性。 -/
theorem finiteOverlapExceptionalModuleComparison_natural (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) {M N : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)} (f : M
      ⟶ N) :
    (finiteOverlapExceptionalModuleEvaluation R a T).map f ≫
      finiteOverlapExceptionalModuleComparison R a h N =
      finiteOverlapExceptionalModuleComparison R a h M ≫
        (finiteOverlapExceptionalIteratedModuleEvaluation R a h).map f :=
  (finiteOverlapExceptionalModuleComparisonNatTrans R a h).naturality f

end SerrePositivity.KST.DerivedBlowup
