module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleComparison
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-!
概要：KST §3.1 の指定の局所加群射から canonical な導来係数拡大比較射を構成する。
方針：局所化の計算同型で指定射を導来制限の射にし、構成済みの延長–制限随伴の逆像を取る。
規約：この段階は対象ごとの指定射。自然性・三重整合性は別に検証する。
使われ方：この射の可逆性として cartesian 条件を定義する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：導来局所評価と加群評価の主局所化の標準自然同型。
方針：構成済みの因子分解等式を自然同型として読む。
規約：KST §3.1。使われ方：対象ごとの計算を自然変換へ束ねる。 -/
def finiteOverlapDerivedEvaluationIso (a : I → R) (T : FiniteOverlapIndex I) :
    moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ ⋙
        finiteOverlapDerivedModuleEvaluation R a T ≅
      finiteOverlapModuleEvaluation R a T ⋙
        moduleToDerived R (FiniteOverlapVertexObject R a T)ᵒᵖ :=
  eqToIso (finiteOverlapDerivedModuleEvaluation_fac R a T)

/-- 概要：実際の図式加群の導来局所評価の標準計算同型。
方針：既存の局所化の因子分解等式を対象で評価する。
規約：KST §3.1。使われ方：指定加群射を導来評価の射として読む。 -/
def finiteOverlapDerivedEvaluationComputation (a : I → R) (T : FiniteOverlapIndex I)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedModuleEvaluation R a T).obj
        ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj M) ≅
      (moduleToDerived R (FiniteOverlapVertexObject R a T)ᵒᵖ).obj
        ((finiteOverlapModuleEvaluation R a T).obj M) :=
  (finiteOverlapDerivedEvaluationIso R a T).app M

/-- 概要：局所 dg 遷移に沿う導来係数制限。
方針：共通基底環上の局所遷移の opposite に既存の導来制限を適用する。
規約：KST §3.1。使われ方：cartesian 比較の随伴前の行先。 -/
abbrev finiteOverlapDerivedTransitionRestriction (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) :=
  dgDerivedRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op

/-- 概要：局所 dg 遷移に沿う実際の導来係数拡大。
方針：graph tensor の標準射影分解による導来延長を使う。
規約：KST §3.1。使われ方：cartesian 比較の始域を作る。 -/
abbrev finiteOverlapDerivedTransitionExtension (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) :=
  dgDerivedExtension R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op

/-- 概要：目標の導来評価を局所制限した関手の標準計算自然同型。
方針：評価の因子分解を右で制限し、局所制限の因子分解を左で評価する。
規約：KST §3.1。使われ方：指定比較射の行先の自然な同定。 -/
def finiteOverlapDerivedRestrictedEvaluationIso (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U) :
    moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ ⋙
        finiteOverlapDerivedModuleEvaluation R a U ⋙
          finiteOverlapDerivedTransitionRestriction R a h ≅
      finiteOverlapIteratedModuleEvaluation R a h ⋙
        moduleToDerived R (FiniteOverlapVertexObject R a T)ᵒᵖ :=
  isoWhiskerRight (finiteOverlapDerivedEvaluationIso R a U)
      (finiteOverlapDerivedTransitionRestriction R a h) ≪≫
    isoWhiskerLeft (finiteOverlapModuleEvaluation R a U)
      (eqToIso (dgDerivedRestriction_fac R (FiniteOverlapVertexObject R a T)ᵒᵖ
        (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op))

/-- 概要：目標の導来評価を局所制限した対象の標準計算同型。
方針：評価の計算同型を導来制限で送り、制限の計算同型を続ける。
規約：KST §3.1。使われ方：指定加群射の行先を導来制限と比較する。 -/
def finiteOverlapDerivedRestrictedEvaluationComputation (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTransitionRestriction R a h).obj
        ((finiteOverlapDerivedModuleEvaluation R a U).obj
          ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj M)) ≅
      (moduleToDerived R (FiniteOverlapVertexObject R a T)ᵒᵖ).obj
        ((finiteOverlapIteratedModuleEvaluation R a h).obj M) :=
  (finiteOverlapDerivedRestrictedEvaluationIso R a h).app M

/-- 概要：実際の図式加群から導来局所制限への指定比較射。
方針：指定単位矢からの加群射を主局所化で送り、両端の標準計算同型を挟む。
規約：KST §3.1。使われ方：導来係数拡大の随伴比較の入力。 -/
def finiteOverlapDerivedRestrictionComparisonOnModule (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedModuleEvaluation R a T).obj
        ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj M) ⟶
      (finiteOverlapDerivedTransitionRestriction R a h).obj
        ((finiteOverlapDerivedModuleEvaluation R a U).obj
          ((moduleToDerived R (BlowupDiagramCoefficientObject R a)ᵒᵖ).obj M)) :=
  (finiteOverlapDerivedEvaluationComputation R a T M).hom ≫
    (moduleToDerived R (FiniteOverlapVertexObject R a T)ᵒᵖ).map
      (finiteOverlapModuleComparison R a h M) ≫
    (finiteOverlapDerivedRestrictedEvaluationComputation R a h M).inv

/-- 概要：主導来局所化の各対象に対する指定の局所制限比較射。
方針：局所化の対象が保持する実際の加群に構成済みの比較を適用する。
規約：KST §3.1、対象ごとの指定射として構成し自然性はまだ別に残す。
使われ方：canonical な導来係数拡大比較の随伴前の射。 -/
def finiteOverlapDerivedRestrictionComparison (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedModuleEvaluation R a T).obj X ⟶
      (finiteOverlapDerivedTransitionRestriction R a h).obj
        ((finiteOverlapDerivedModuleEvaluation R a U).obj X) :=
  finiteOverlapDerivedRestrictionComparisonOnModule R a h X.as.obj

/-- 概要：局所導来係数拡大から目標の評価への canonical な比較射。
方針：指定制限比較を、構成済みの導来延長–制限随伴の Hom 同値の逆で移す。
規約：KST §3.1、任意の射や同型の存在を仮定しない。
使われ方：この指定射の可逆性を cartesian 条件に使う。 -/
def finiteOverlapDerivedExtensionComparison (a : I → R) {T U : FiniteOverlapIndex I}
    (h : T ≤ U) (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTransitionExtension R a h).obj
        ((finiteOverlapDerivedModuleEvaluation R a T).obj X) ⟶
      (finiteOverlapDerivedModuleEvaluation R a U).obj X :=
  ((dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ
    (finiteOverlapLocalDGTransition R a h).op).homEquiv _ _).symm
      (finiteOverlapDerivedRestrictionComparison R a h X)

/-- 概要：構成した導来係数拡大比較の随伴像は元の指定制限比較に一致する。
方針：構成済みの Hom 同値の逆元律を使う。
規約：KST §3.1。使われ方：cartesian 条件に用いる射の経路の確認。 -/
theorem finiteOverlapDerivedExtensionComparison_adjunct (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (dgDerivedExtensionRestrictionAdjunction R (FiniteOverlapVertexObject R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op).homEquiv _ _
      (finiteOverlapDerivedExtensionComparison R a h X) =
      finiteOverlapDerivedRestrictionComparison R a h X :=
  Equiv.apply_symm_apply _ _

end SerrePositivity.KST.DerivedBlowup
