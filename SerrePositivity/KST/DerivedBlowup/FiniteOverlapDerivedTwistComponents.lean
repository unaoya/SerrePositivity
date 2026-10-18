module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistAction
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation

/-!
概要：KST §3.1 の導来捻りの指定比較を主局所化前へ戻す。
方針：標準導来制限比較の実加群上の成分を具体的捻りへ適用する。
規約：指数の等式による移送も主局所化の像として計算する。
使われ方：捻り作用の結合・単位整合性を導来圏へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：導来捻り作用は実加群射の主局所化像で元の捻り射を与える。
方針：指定導来制限の生成射の計算公式を使う。
規約：KST §3.1。使われ方：導来合成経路を加群圏へ戻す。 -/
theorem finiteOverlapDerivedTwistAction_map_Q (m : ℤ)
    {M N : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)} (f : M ⟶ N) :
    (finiteOverlapDerivedTwistAction R a m).map
        ((moduleToDerived R
          (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map f) =
      (moduleToDerived R
        (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map
        ((finiteOverlapTwistAction R a m).map f) := rfl

/-- 概要：導来捻りの零比較の実加群上の順成分は元の比較の主局所化像。
方針：標準導来制限単位比較の計算公式を適用する。
規約：KST §3.1。使われ方：導来単位条件。 -/
theorem finiteOverlapDerivedTwistActionZeroIso_hom_app_Q
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTwistActionZeroIso R a).hom.app
        ((moduleToDerived R
          (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj M) =
      (moduleToDerived R
        (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map
        ((finiteOverlapTwistActionZeroIso R a).hom.app M) :=
  transitionDerivedRestrictionIdIso_hom_app_Q (finiteOverlapTwistDGFunctor R a 0)
    (finiteOverlapTwistDGFunctor_zero R a) M

set_option maxHeartbeats 2000000 in
-- 二つの具体的 Koszul 係数自己関手の導来合成比較の型を照合するために必要。
/-- 概要：導来捻りの加法比較の実加群上の順成分は元の比較の主局所化像。
方針：標準導来制限合成比較の計算公式を適用する。
規約：KST §3.1。使われ方：導来結合条件。 -/
theorem finiteOverlapDerivedTwistActionAddIso_hom_app_Q (m n : ℤ)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTwistActionAddIso R a m n).hom.app
        ((moduleToDerived R
          (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj M) =
      (moduleToDerived R
        (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map
        ((finiteOverlapTwistActionAddIso R a m n).hom.app M) :=
  transitionDerivedRestrictionCompIso_hom_app_Q (finiteOverlapTwistDGFunctor R a m)
    (finiteOverlapTwistDGFunctor R a n) (finiteOverlapTwistDGFunctor R a (m + n))
    (finiteOverlapTwistDGFunctor_add R a m n) M

/-- 概要：指数の等式による導来捻り対象の移送は元の移送の主局所化像。
方針：指数の等式を消去し、関手の恒等保存を使う。
規約：KST §3.1。使われ方：整数和の結合・単位による移送を導来化する。 -/
theorem finiteOverlapDerivedTwistAction_transport_Q {m n : ℤ} (h : m = n)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    eqToHom (congrArg (fun k => (finiteOverlapDerivedTwistAction R a k).obj
      ((moduleToDerived R
        (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj M)) h) =
      (moduleToDerived R
        (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map
        (eqToHom (congrArg (fun k => (finiteOverlapTwistAction R a k).obj M) h)) := by
  subst n
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.KST.DerivedBlowup
