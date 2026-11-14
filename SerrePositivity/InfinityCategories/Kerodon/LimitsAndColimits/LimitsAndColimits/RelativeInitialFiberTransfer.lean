module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalFiberTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CartesianInitialBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialBoundaryIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryTransport

/-!
概要：共通の底への cartesian 輸送を保つ射では、fiber の相対始対象性を全空間へ移せる。
方針：fiber の反転同型で相対終対象の移送に還元する。
規約：射自身の cartesian fibration 性は要求しない。
使われ方：Kerodon Proposition 7.1.5.19（Tag 02WU）、相対 join の普遍余錐の充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：相対始点境界充填は射と頂点を反転すると終点境界充填となる。
方針：二重反転の同型で移してから既存の反転による充填を使う。
規約：単体集合は任意。
使われ方：fiber 内の相対始対象性の双対化。 -/
lemma kanInitialBoundaryLifting_op_terminal {E F : SSet.{u}} {f : E ⟶ F}
    {x : E _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting f x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (SSet.opFunctor.map f) (SSet.opObjEquiv.symm x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_of_initialBoundaryLifting_op
  exact hx.map_iso (SSet.opFunctorCompOpFunctorIso.app E).symm
    (SSet.opFunctorCompOpFunctorIso.app F).symm (by
      simpa using (SSet.opFunctorCompOpFunctorIso.inv.naturality f).symm)

/-- 概要：fiber の相対始点境界充填は輸送を保つ射の全空間へ移る。
方針：両射影を反転し、fiber 同型で終点境界充填を移して一般の輸送補題を適用する。
規約：両射影は cartesian fibration、対象の射は inner fibration。
使われ方：余錐の fiber の普遍性から相対 join の全空間の充填を得る。 -/
lemma kanInitialBoundaryLifting_of_fiber_map {E F B : SSet.{u}}
    [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration q]
    (f : E ⟶ F) [InnerFibration f] (hf : f ≫ q = p)
    (hpres : ∀ e : E _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e →
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q (f.app (Opposite.op ⦋1⦌) e))
    (b : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting f x.val := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cartesianFibration_op_toCocartesianHornFibration p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cartesianFibration_op_toCocartesianHornFibration q
  let hfop : SSet.opFunctor.map f ≫ SSet.opFunctor.map q = SSet.opFunctor.map p := by
    rw [← Functor.map_comp, hf]
  let xop := (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p b).hom.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x)
  have hnat : (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (SSet.opFunctor.map p) (SSet.opFunctor.map q)
        (SSet.opFunctor.map f) hfop (SSet.opObjEquiv.symm b) =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso q b).hom := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl
  have hxop := (kanInitialBoundaryLifting_op_terminal hx).map_iso
    (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso p b) (_root_.SerrePositivity.InfinityCategories.HTT.Section2_1_3.vertexFiberOpIso q b) hnat
  have hpresop (e : E.op _⦋1⦌)
      (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p) e) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map q)
        ((SSet.opFunctor.map f).app (Opposite.op ⦋1⦌) e) := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_isCocartesianEdge_op p (SSet.opObjEquiv e) he
    exact (hpres _ hc).op
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_terminalBoundaryLifting_op
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanTerminalBoundaryLifting_of_fiber_map (SSet.opFunctor.map p) (SSet.opFunctor.map q)
    (SSet.opFunctor.map f) hfop hpresop (SSet.opObjEquiv.symm b) xop hxop

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
