module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalDerivedNaturality

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の Koszul 局所模型の指定導来制限比較の計算。
方針：標準評価同型の対象成分を恒等に簡約する。
規約：元の指定加群比較の主局所化像を計算する。
使われ方：一対象正規表示との canonical な比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：元の導来評価の標準同型の順成分は恒等。
方針：因子分解の対象等式を簡約する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：指定導来比較の始域の計算。 -/
theorem finiteOverlapExceptionalDerivedEvaluationIso_hom_app (a : I → R) (T : FiniteOverlapIndex I)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (finiteOverlapExceptionalDerivedEvaluationIso R a T).hom.app M = 𝟙 _ := by
  simp only [finiteOverlapExceptionalDerivedEvaluationIso, eqToIso.hom, eqToHom_app]
  rfl

/-- 概要：元の導来評価の標準同型の逆成分は恒等。
方針：逆方向の因子分解の対象等式を簡約する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：反復制限の計算同型の簡約。 -/
theorem finiteOverlapExceptionalDerivedEvaluationIso_inv_app (a : I → R) (T : FiniteOverlapIndex I)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (finiteOverlapExceptionalDerivedEvaluationIso R a T).inv.app M = 𝟙 _ := by
  simp only [finiteOverlapExceptionalDerivedEvaluationIso, eqToIso.inv, eqToHom_app]
  rfl

set_option maxHeartbeats 2000000 in
-- 元の局所化環の反復導来制限と評価の型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底制限後の局所 dg 構造を照合するために必要。
/-- 概要：元の反復導来制限の計算同型の逆成分は恒等。
方針：評価同型と局所制限の因子分解の対象成分を簡約する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：指定制限比較の行先の計算。 -/
theorem finiteOverlapExceptionalDerivedRestrictedEvaluationIso_inv_app (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (finiteOverlapExceptionalDerivedRestrictedEvaluationIso R a h).inv.app M = 𝟙 _ := by
  change (eqToIso (dgDerivedRestriction_fac R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
      (FiniteOverlapExceptionalVertexObject R a U)ᵒᵖ (finiteOverlapExceptionalLocalDGTransition
        R a h).op)).inv.app
      ((finiteOverlapExceptionalModuleEvaluation R a U).obj M) ≫
      (finiteOverlapExceptionalDerivedTransitionRestriction R a h).map
        ((finiteOverlapExceptionalDerivedEvaluationIso R a U).inv.app M) = _
  rw [finiteOverlapExceptionalDerivedEvaluationIso_inv_app]
  dsimp only [Functor.comp]
  rw [CategoryTheory.Functor.map_id]
  simp only [eqToIso.inv, eqToHom_refl, NatTrans.id_app, Category.comp_id]
  rfl

set_option maxHeartbeats 2000000 in
-- 二つの局所化環の指定加群射と主局所化像を照合するために必要。
/-- 概要：元の指定導来制限比較は実加群上で指定加群比較の局所化像。
方針：延長の成分を前延長へ戻し、計算同型の恒等成分を消去する。
規約：KST v4 §3.1・Lemma 3.6（pp.11–14）。使われ方：局所表示の変更との整合性の計算。 -/
theorem finiteOverlapExceptionalDerivedRestrictionNatTrans_app_Q_map (a : I → R)
    {T U : FiniteOverlapIndex I} (h : T ≤ U)
    (M : AllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    (finiteOverlapExceptionalDerivedRestrictionNatTrans R a h).app
        ((moduleToDerived R (DiagramModuleCoefficientObject
          (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).obj M) =
      (moduleToDerived R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ).map
        (finiteOverlapExceptionalModuleComparison R a h M) := by
  rw [show (finiteOverlapExceptionalDerivedRestrictionNatTrans R a h).app
      ((moduleToDerived R (DiagramModuleCoefficientObject
        (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).obj M) =
      (finiteOverlapExceptionalDerivedRestrictionPreNatTrans R a h).app M from
    Localization.Construction.NatTransExtension.app_eq _ M]
  change (finiteOverlapExceptionalDerivedEvaluationIso R a T).hom.app M ≫
      (moduleToDerived R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ).map
        (finiteOverlapExceptionalModuleComparison R a h M) ≫
      (finiteOverlapExceptionalDerivedRestrictedEvaluationIso R a h).inv.app M = _
  rw [finiteOverlapExceptionalDerivedEvaluationIso_hom_app,
    finiteOverlapExceptionalDerivedRestrictedEvaluationIso_inv_app]
  dsimp only [Functor.comp]
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.KST.DerivedBlowup
