module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceInitial
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationTerminalLift
public import SerrePositivity.InfinityCategories.Core.LeftFibrationTerminalFiber

/-!
概要：固定始域圏の終対象を終点とする余錐は、反復 coslice 内でも終対象になる。
方針：coslice の始対象から終対象上の fiber の可縮性を得て、同じ指定点へ戻す。
規約：元の終対象の存在は仮定し、局所性や反射の存在は主張しない。
使われ方：HTT 5.5.5.12–14 の合成の fiber による高次の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

private lemma coslice_isTerminal_of_terminal_target {E : SSet.{u}} [Quasicategory E]
    (t s : E _⦋0⦌) (hs : IsTerminalVertex s)
    (c : JoinCocone (SSet.yonedaEquiv.symm t)) (hc : c.vertex = s) :
    IsTerminalVertex (X := sliceUnder (SSet.yonedaEquiv.symm t)) c := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm t)
  have hcontr : IsContractibleKan (vertexFiber p s) :=
    leftFibration_terminalFiber_isContractibleKan p (cosliceIdentityCone_isInitialVertex t) hs
  let c' : (vertexFiber p s) _⦋0⦌ := ⟨c, by
    change c.vertex = PinchedHom.constant s 0
    rw [pinchedConstant_zero, hc]⟩
  exact leftFibration_isTerminalVertex_of_contractibleFiber p s hs hcontr c'

/-- 指定した終対象へ至る任意の余錐は、同じ固定始域圏内の反復 coslice の終対象。 -/
lemma generatedSource_terminal_coslice_isTerminal
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    (t : (generatedSourceCategory edges x) _⦋0⦌)
    (c : JoinCocone (SSet.yonedaEquiv.symm t)) (hc : c.vertex = s) :
    IsTerminalVertex (X := sliceUnder (SSet.yonedaEquiv.symm t)) c :=
  coslice_isTerminal_of_terminal_target t s hs c hc

/-- 終対象の恒等余錐は、同じ終対象の下の反復 coslice でも終対象。 -/
lemma generatedSource_terminal_identity_isTerminal
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s) :
    IsTerminalVertex (cosliceIdentityCone s) :=
  generatedSource_terminal_coslice_isTerminal edges x s hs s (cosliceIdentityCone s)
    (cosliceIdentityCone_projection s)

/-- 反復 coslice での恒等余錐への写像空間は、全高次を含めて可縮。 -/
lemma generatedSource_terminal_identity_mapping_contractible
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    (c : JoinCocone (SSet.yonedaEquiv.symm s)) :
    IsContractibleKan (pinchedHom (X := sliceUnder (SSet.yonedaEquiv.symm s))
      c (cosliceIdentityCone s)) :=
  (generatedSource_terminal_identity_isTerminal edges x s hs).pinchedHom_isContractibleKan c

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
