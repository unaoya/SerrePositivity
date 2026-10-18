module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapComparisonComponents
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapBaseDGFunctoriality
public import SerrePositivity.KST.DerivedBlowup.TransitionRestrictionCoherence

/-!
概要：KST §3.1 の局所 dg 遷移に沿う加群制限の標準合成比較。
方針：局所 dg 遷移の合成等式を既存の加群制限合成同型へ接続する。
規約：指定比較の合成条件に用いる同型を固定する。
使われ方：canonical な局所加群比較の三重整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：選択 pivot に沿う局所 dg 遷移の合成律。
方針：共通基底環上の有限重なりの合成律を適用する。
規約：KST §3.1。使われ方：局所加群制限の合成同型。 -/
theorem finiteOverlapLocalDGTransition_comp (a : I → R)
    {T U V : FiniteOverlapIndex I} (h : T ≤ U) (g : U ≤ V) :
    (finiteOverlapLocalDGTransition R a h).comp (finiteOverlapLocalDGTransition R a g) =
      finiteOverlapLocalDGTransition R a (h.trans g) :=
  finiteOverlapBaseDGTransition_comp R a _ _ _ h g
    (finiteOverlapIndexPivot_mem T) (finiteOverlapIndexPivot_mem U)

/-- 概要：選択 pivot に沿う恒等局所 dg 遷移は恒等関手。
方針：共通基底環上の有限重なりの恒等律を適用する。
規約：KST §3.1。使われ方：局所加群制限の単位同型。 -/
theorem finiteOverlapLocalDGTransition_id (a : I → R) (T : FiniteOverlapIndex I) :
    finiteOverlapLocalDGTransition R a (le_refl T) = DGFunctor.id _ :=
  finiteOverlapBaseDGTransition_id R a _ T.val (finiteOverlapIndexPivot_mem T)

/-- 概要：恒等局所遷移に沿う加群制限から恒等関手への標準同型。
方針：局所 dg 恒等律で移送し、既存の制限単位同型を続ける。
規約：KST §3.1。使われ方：指定局所加群比較の単位条件。 -/
def finiteOverlapLocalModuleRestrictionIdIso (a : I → R) (T : FiniteOverlapIndex I) :
    moduleRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a T)ᵒᵖ
        (finiteOverlapLocalDGTransition R a (le_refl T)).op.op ≅ 𝟭 _ :=
  transitionRestrictionIdIso (finiteOverlapLocalDGTransition R a (le_refl T))
    (finiteOverlapLocalDGTransition_id R a T)

set_option maxHeartbeats 4000000 in
-- 局所化 dg 模型と制限の恒等比較の型を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 基底環への制限のモノイダル構造を比較するために必要。
/-- 概要：恒等局所制限の標準同型は underlying 複体上で恒等。
方針：等式移送と既存の加群制限単位同型を評価する。
規約：KST §3.1。使われ方：指定加群比較の単位条件の評価。 -/
theorem finiteOverlapLocalModuleRestrictionIdIso_hom_eval (a : I → R)
    (T : FiniteOverlapIndex I)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    (moduleEvaluation R (FiniteOverlapVertexObject R a T)ᵒᵖ (op .point)).map
      ((finiteOverlapLocalModuleRestrictionIdIso R a T).hom.app
        ((finiteOverlapModuleEvaluation R a T).obj M)) = 𝟙 _ := by
  exact transitionRestrictionIdIso_eval (finiteOverlapLocalDGTransition R a (le_refl T))
    (finiteOverlapLocalDGTransition_id R a T)
    ((finiteOverlapModuleEvaluation R a T).obj M) .point

/-- 概要：局所遷移に沿う二段の加群制限から直接制限への標準同型。
方針：加群制限の合成比較に dg 遷移の合成等式を続ける。
規約：KST §3.1。使われ方：三重加群比較の行先を揃える。 -/
def finiteOverlapLocalModuleRestrictionCompIso (a : I → R)
    {T U V : FiniteOverlapIndex I} (h : T ≤ U) (g : U ≤ V) :
    moduleRestriction R (FiniteOverlapVertexObject R a U)ᵒᵖ
        (FiniteOverlapVertexObject R a V)ᵒᵖ (finiteOverlapLocalDGTransition R a g).op.op ⋙
      moduleRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
        (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op.op ≅
    moduleRestriction R (FiniteOverlapVertexObject R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a V)ᵒᵖ
        (finiteOverlapLocalDGTransition R a (h.trans g)).op.op :=
  transitionRestrictionCompIso (finiteOverlapLocalDGTransition R a h)
    (finiteOverlapLocalDGTransition R a g) (finiteOverlapLocalDGTransition R a (h.trans g))
    (finiteOverlapLocalDGTransition_comp R a h g)

end SerrePositivity.KST.DerivedBlowup
