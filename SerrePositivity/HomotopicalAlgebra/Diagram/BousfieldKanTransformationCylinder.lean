module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanOverTransformationNaturality
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTerminalWeightDiagram

/-!
概要：指定添字自然変換から得るBK重みの円柱と、元の比較射による両端。
方針：Overのホモトピーを添字全体に束ね、nerveの合成保存で端点を照合する。
使われ方：HTT 4.2.4.4、RR02(a)の余単位の実現への移送。
規約：指定された重み比較と自然変換の像をそのまま保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {P Q : L ⥤ K} (α : P ⟶ Q)

/-- 元のOverホモトピーを、制限BK重みへの円柱に束ねる。 -/
def bousfieldKanTransformationCylinder :
    (weightedParameterFunctor (bousfieldKanWeight Lᵒᵖ)).obj (Δ[1] : SSet.{w}) ⟶
      P.op ⋙ bousfieldKanWeight Kᵒᵖ where
  app e := (overTransformationHomotopy α e.unop).h
  naturality i j f := overTransformationHomotopy_naturality α f.unop

/-- 始端はQによる添字比較の後に指定変換の反対射を移送した射。 -/
lemma bousfieldKanTransformationCylinder_zero :
    terminalWeightEndpoint (K := L) 0 ≫ bousfieldKanTransformationCylinder α =
      bousfieldKanWeightPost Q.op ≫
        Functor.whiskerRight (NatTrans.op α) (bousfieldKanWeight Kᵒᵖ) := by
  apply NatTrans.ext
  funext e
  change SSet.ι₀ ≫ (overTransformationHomotopy α e.unop).h = _
  rw [(overTransformationHomotopy α e.unop).h₀]
  exact nerveFunctor.map_comp (Over.post Q.op (X := e)).toCatHom
    (Over.map (α.app e.unop).op).toCatHom

/-- 終端はPによる元の指定添字比較そのもの。 -/
lemma bousfieldKanTransformationCylinder_one :
    terminalWeightEndpoint (K := L) 1 ≫ bousfieldKanTransformationCylinder α =
      bousfieldKanWeightPost P.op := by
  apply NatTrans.ext
  funext e
  exact (overTransformationHomotopy α e.unop).h₁

end SerrePositivity.DiagramModel.FrameWeightRealization
