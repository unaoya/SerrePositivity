module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistActionCoherence
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDerivedTwistComponents

/-!
概要：KST §3.1 の整数捻り作用の主導来圏上の結合・単位整合性。
方針：局所化の対象対応で実加群へ戻し、指定加群比較の可換式を主局所化で送る。
規約：指数の和の等式による対象移送を省略しない。
使われ方：導来捻りの指定加法・単位比較の経路を固定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

set_option maxHeartbeats 2000000 in
-- 三段の指定導来比較を同じ実加群の局所化像へ照合するために必要。
/-- 概要：主導来圏の三段捻りの指定加法比較は結合整合性を満たす。
方針：実加群上の指定経路へ戻し、証明済みの加群段階の結合条件を送る。
規約：KST §3.1。使われ方：導来捻り作用の合成条件。 -/
theorem finiteOverlapDerivedTwistActionAddIso_assoc (m n p : ℤ)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTwistActionAddIso R a m n).hom.app
        ((finiteOverlapDerivedTwistAction R a p).obj X) ≫
        (finiteOverlapDerivedTwistActionAddIso R a (m + n) p).hom.app X ≫
        eqToHom (congrArg (fun k => (finiteOverlapDerivedTwistAction R a k).obj X)
          (add_assoc m n p)) =
      (finiteOverlapDerivedTwistAction R a m).map
          ((finiteOverlapDerivedTwistActionAddIso R a n p).hom.app X) ≫
        (finiteOverlapDerivedTwistActionAddIso R a m (n + p)).hom.app X := by
  obtain ⟨M, hM⟩ := (Localization.Construction.objEquiv
    (moduleQuasiIso R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ)).surjective X
  change (moduleToDerived R
    (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj M = X at hM
  subst X
  change (finiteOverlapDerivedTwistActionAddIso R a m n).hom.app
      ((moduleToDerived R
        (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj
        ((finiteOverlapTwistAction R a p).obj M)) ≫ _ = _
  rw [finiteOverlapDerivedTwistActionAddIso_hom_app_Q,
    finiteOverlapDerivedTwistActionAddIso_hom_app_Q,
    finiteOverlapDerivedTwistAction_transport_Q R a (add_assoc m n p),
    finiteOverlapDerivedTwistActionAddIso_hom_app_Q,
    finiteOverlapDerivedTwistActionAddIso_hom_app_Q,
    finiteOverlapDerivedTwistAction_map_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map)
      (finiteOverlapTwistActionAddIso_assoc R a m n p M)

set_option maxHeartbeats 2000000 in
-- 左単位の指数移送と指定導来比較を実加群へ戻すために必要。
/-- 概要：導来捻りの加法比較は左の零指数で指定単位比較に一致。
方針：実加群上の成分を計算し、加群段階の左単位条件を送る。
規約：KST §3.1。使われ方：導来捻り作用の左単位条件。 -/
theorem finiteOverlapDerivedTwistActionAddIso_zero_left (m : ℤ)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTwistActionAddIso R a 0 m).hom.app X ≫
        eqToHom (congrArg (fun k => (finiteOverlapDerivedTwistAction R a k).obj X) (zero_add m)) =
      (finiteOverlapDerivedTwistActionZeroIso R a).hom.app
        ((finiteOverlapDerivedTwistAction R a m).obj X) := by
  obtain ⟨M, hM⟩ := (Localization.Construction.objEquiv
    (moduleQuasiIso R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ)).surjective X
  change (moduleToDerived R
    (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj M = X at hM
  subst X
  change _ = (finiteOverlapDerivedTwistActionZeroIso R a).hom.app
    ((moduleToDerived R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj
      ((finiteOverlapTwistAction R a m).obj M))
  rw [finiteOverlapDerivedTwistActionAddIso_hom_app_Q,
    finiteOverlapDerivedTwistAction_transport_Q R a (zero_add m),
    finiteOverlapDerivedTwistActionZeroIso_hom_app_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map)
      (finiteOverlapTwistActionAddIso_zero_left R a m M)

set_option maxHeartbeats 2000000 in
-- 右単位の指数移送と指定導来比較を実加群へ戻すために必要。
/-- 概要：導来捻りの加法比較は右の零指数で単位比較の作用像に一致。
方針：実加群上の成分を計算し、加群段階の右単位条件を送る。
規約：KST §3.1。使われ方：導来捻り作用の右単位条件。 -/
theorem finiteOverlapDerivedTwistActionAddIso_zero_right (m : ℤ)
    (X : DerivedAllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (finiteOverlapDerivedTwistActionAddIso R a m 0).hom.app X ≫
        eqToHom (congrArg (fun k => (finiteOverlapDerivedTwistAction R a k).obj X) (add_zero m)) =
      (finiteOverlapDerivedTwistAction R a m).map
        ((finiteOverlapDerivedTwistActionZeroIso R a).hom.app X) := by
  obtain ⟨M, hM⟩ := (Localization.Construction.objEquiv
    (moduleQuasiIso R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ)).surjective X
  change (moduleToDerived R
    (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).obj M = X at hM
  subst X
  rw [finiteOverlapDerivedTwistActionAddIso_hom_app_Q,
    finiteOverlapDerivedTwistAction_transport_Q R a (add_zero m),
    finiteOverlapDerivedTwistActionZeroIso_hom_app_Q, finiteOverlapDerivedTwistAction_map_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R
      (DiagramModuleCoefficientObject (finiteOverlapDGAlgebraDiagram R a))ᵒᵖ).map)
      (finiteOverlapTwistActionAddIso_zero_right R a m M)

end SerrePositivity.KST.DerivedBlowup
