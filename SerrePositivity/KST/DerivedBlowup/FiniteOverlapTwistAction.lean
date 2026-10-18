module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistFunctorCoherence
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistModule
public import SerrePositivity.KST.DerivedBlowup.TransitionRestrictionCoherence
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionCoherence

/-!
概要：KST §3.1 の捻りを全図式加群と主導来圏に作用させる。
方針：整数捻りの係数 dg 関手に沿う制限を取り、標準の単位・合成比較を適用する。
規約：指定比較経路を使う。高次の全整合性や層との比較はここでは結論しない。
使われ方：大域 O(m) の加群・導来対象の計算と逆捻り。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：整数捻りの全図式加群圏上の作用。
方針：指定 dg 自己関手に沿う既存の加群制限を使う。
規約：KST §3.1。使われ方：実際の O(m) と一般加群の捻り。 -/
abbrev finiteOverlapTwistAction (a : I → R) (m : ℤ) :=
  moduleRestriction R (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ
    (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ
    (finiteOverlapTwistDGFunctor R a m).op.op

/-- 概要：整数捻りの全図式主導来圏上の作用。
方針：指定 dg 自己関手に沿う導来制限を使う。
規約：KST §3.1。使われ方：導来 O(m) と一般導来対象の捻り。 -/
abbrev finiteOverlapDerivedTwistAction (a : I → R) (m : ℤ) :=
  dgDerivedRestriction R (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ
    (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ
    (finiteOverlapTwistDGFunctor R a m).op

/-- 概要：構造加群に捻り作用を施すと構成済みの O(m) を得る。
方針：制限による両方の定義を読む。
規約：KST §3.1。使われ方：作用と指定捻り対象の接続。 -/
theorem finiteOverlapTwistAction_structure (a : I → R) (m : ℤ) :
    (finiteOverlapTwistAction R a m).obj
        (diagramStructureModule (finiteOverlapDGAlgebraDiagram R a)) =
      finiteOverlapTwistModule R a m := rfl

/-- 概要：導来構造対象への捻り作用は指定導来 O(m) に一致する。
方針：主局所化上の導来制限の因子分解等式を構造加群で評価する。
規約：KST §3.1。使われ方：指定作用と実際の導来捻り対象の接続。 -/
theorem finiteOverlapDerivedTwistAction_structure (a : I → R) (m : ℤ) :
    (finiteOverlapDerivedTwistAction R a m).obj
        (derivedDiagramStructureModule (finiteOverlapDGAlgebraDiagram R a)) =
      derivedFiniteOverlapTwistModule R a m :=
  congrArg (fun G => G.obj (diagramStructureModule (finiteOverlapDGAlgebraDiagram R a)))
    (dgDerivedRestriction_fac R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ
      (finiteOverlapTwistDGFunctor R a m).op)

/-- 概要：零捻り作用から恒等作用への指定自然同型。
方針：係数 dg 関手の零捻り等式を標準制限単位比較へ渡す。
規約：KST §3.1。使われ方：構造加群への特殊化。 -/
def finiteOverlapTwistActionZeroIso (a : I → R) :
    finiteOverlapTwistAction R a 0 ≅ 𝟭 _ :=
  transitionRestrictionIdIso _ (finiteOverlapTwistDGFunctor_zero R a)

/-- 概要：反復捻りと指数の和の作用の指定自然同型。
方針：係数 dg 関手の加法等式を標準制限合成比較へ渡す。
規約：KST §3.1、制限の合成順序を表示する。
使われ方：加群圏での捻りと逆捻りの計算。 -/
def finiteOverlapTwistActionAddIso (a : I → R) (m n : ℤ) :
    finiteOverlapTwistAction R a n ⋙ finiteOverlapTwistAction R a m ≅
      finiteOverlapTwistAction R a (m + n) :=
  transitionRestrictionCompIso _ _ _ (finiteOverlapTwistDGFunctor_add R a m n)

/-- 概要：主導来圏の零捻りから恒等作用への指定自然同型。
方針：係数 dg 関手の零捻り等式を標準導来制限単位比較へ渡す。
規約：KST §3.1。使われ方：導来構造加群への特殊化。 -/
def finiteOverlapDerivedTwistActionZeroIso (a : I → R) :
    finiteOverlapDerivedTwistAction R a 0 ≅ 𝟭 _ :=
  transitionDerivedRestrictionIdIso _ (finiteOverlapTwistDGFunctor_zero R a)

/-- 概要：主導来圏の反復捻りと指数の和の指定自然同型。
方針：加法等式を標準導来制限合成比較へ渡す。
規約：KST §3.1、局所化前の指定経路を延長した比較を使う。
使われ方：導来対象での捻りと逆捻りの計算。 -/
def finiteOverlapDerivedTwistActionAddIso (a : I → R) (m n : ℤ) :
    finiteOverlapDerivedTwistAction R a n ⋙ finiteOverlapDerivedTwistAction R a m ≅
      finiteOverlapDerivedTwistAction R a (m + n) :=
  transitionDerivedRestrictionCompIso _ _ _ (finiteOverlapTwistDGFunctor_add R a m n)

/-- 概要：加群圏の逆捻りから恒等作用への指定自然同型。
方針：係数 dg 関手の両側逆等式を合成比較と単位比較で送る。
規約：KST §3.1。使われ方：捻りの可逆性。 -/
def finiteOverlapTwistActionInverseIso (a : I → R) (m : ℤ) :
    finiteOverlapTwistAction R a (-m) ⋙ finiteOverlapTwistAction R a m ≅ 𝟭 _ :=
  transitionRestrictionCompIso _ _ _ (finiteOverlapTwistDGFunctor_neg_comp R a m) ≪≫
    transitionRestrictionIdIso _ rfl

/-- 概要：主導来圏の逆捻りから恒等作用への指定自然同型。
方針：係数 dg 関手の逆等式を標準導来合成・単位比較で送る。
規約：KST §3.1。使われ方：導来捻り作用の可逆性。 -/
def finiteOverlapDerivedTwistActionInverseIso (a : I → R) (m : ℤ) :
    finiteOverlapDerivedTwistAction R a (-m) ⋙ finiteOverlapDerivedTwistAction R a m ≅ 𝟭 _ :=
  transitionDerivedRestrictionCompIso _ _ _ (finiteOverlapTwistDGFunctor_neg_comp R a m) ≪≫
    transitionDerivedRestrictionIdIso _ rfl

end SerrePositivity.KST.DerivedBlowup
