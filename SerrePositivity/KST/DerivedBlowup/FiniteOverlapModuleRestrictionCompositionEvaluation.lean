module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapModuleRestrictionCoherence

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

set_option maxHeartbeats 4000000 in
-- 三つの局所化環の dg 構造と制限合成同型の成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 共通基底環への制限で複数のモノイダル構造を比較するために必要。
/-- 概要：局所制限の標準合成同型の対象移送を含む評価公式。
方針：一般の dg 遷移の合成比較の評価公式を具体的な包含へ適用する。
規約：KST §3.1、対象等式の移送を明示した形を保つ。
使われ方：指定加群比較の合成条件の評価。 -/
theorem finiteOverlapLocalModuleRestrictionCompIso_hom_eval (a : I → R)
    {T U V : FiniteOverlapIndex I} (h : T ≤ U) (g : U ≤ V)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    type_of% (transitionRestrictionCompIso_eval (finiteOverlapLocalDGTransition R a h)
      (finiteOverlapLocalDGTransition R a g) (finiteOverlapLocalDGTransition R a (h.trans g))
      (finiteOverlapLocalDGTransition_comp R a h g)
      ((finiteOverlapModuleEvaluation R a V).obj M) .point) :=
  transitionRestrictionCompIso_eval (finiteOverlapLocalDGTransition R a h)
    (finiteOverlapLocalDGTransition R a g) (finiteOverlapLocalDGTransition R a (h.trans g))
    (finiteOverlapLocalDGTransition_comp R a h g)
    ((finiteOverlapModuleEvaluation R a V).obj M) .point

/-- 概要：図式加群を制限した場合の標準合成同型の成分は恒等。
方針：一般評価の対象移送は、頂点で一定の underlying 複体上では恒等になる。
規約：KST §3.1、一般補題の型を継承して局所化係数構造の再展開を避ける。
使われ方：三重加群比較を underlying 図式の関手性に戻す。 -/
theorem finiteOverlapLocalModuleRestrictionCompIso_hom_eval_id (a : I → R)
    {T U V : FiniteOverlapIndex I} (h : T ≤ U) (g : U ≤ V)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    type_of% ((finiteOverlapLocalModuleRestrictionCompIso_hom_eval R a h g M).trans
      (show _ = 𝟙 _ from rfl)) :=
  (finiteOverlapLocalModuleRestrictionCompIso_hom_eval R a h g M).trans
    (show _ = 𝟙 _ from rfl)

/-- 概要：最初の包含で制限した二番目の指定比較の評価。
方針：制限の射の評価公式と任意の局所対象での指定比較の評価を合成する。
規約：KST §3.1、型は既存評価公式から継承する。
使われ方：三重比較の中央の射の計算。 -/
theorem finiteOverlapRestrictedModuleComparison_eval (a : I → R)
    {T U V : FiniteOverlapIndex I} (h : T ≤ U) (g : U ≤ V)
    (M : AllDiagramModules (finiteOverlapDGAlgebraDiagram R a)) :
    type_of% ((moduleRestriction_map_eval R (FiniteOverlapVertexObject R a T)ᵒᵖ
      (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op.op
      (finiteOverlapModuleComparison R a g M) (op .point)).trans
        (finiteOverlapModuleComparison_eval_any R a g M _)) :=
  (moduleRestriction_map_eval R (FiniteOverlapVertexObject R a T)ᵒᵖ
    (FiniteOverlapVertexObject R a U)ᵒᵖ (finiteOverlapLocalDGTransition R a h).op.op
    (finiteOverlapModuleComparison R a g M) (op .point)).trans
      (finiteOverlapModuleComparison_eval_any R a g M _)

end SerrePositivity.KST.DerivedBlowup
