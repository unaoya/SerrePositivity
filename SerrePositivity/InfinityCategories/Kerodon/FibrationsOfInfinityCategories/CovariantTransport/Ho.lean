module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Witness

/-!
概要：transport の選択と各 fiber のホモトピー圏間の関手。
方針：可縮な選択空間から一点を選び、hoFunctor で射を写す。
規約：底のホモトピー圏上の関手への合成則は別の工程で扱う。
使われ方：Kerodon §5.2.5（Tag 01VT）、transport のホモトピー圏への移行。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：辺に沿う cocartesian transport 関手を一つ選ぶ。
方針：可縮な選択空間の非空性から一点を選び、その終点関手を取る。
規約：選択した関手の厳密な同一性は要求しない。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の利用側 API。 -/
noncomputable def cocartesianTransport {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e
    (Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceSpace_isContractibleKan p e).nonempty)

/-- 概要：選択した transport 関手は cocartesian な prism の証人を持つ。
方針：選択空間の任意の頂点について得た証人を使う。
規約：始点と底の辺の族は厳密に保つ。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、選択した関手の正当性。 -/
lemma cocartesianTransport_isTransport {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianTransport p e (cocartesianTransport p e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice_witness p e _

/-- 概要：辺に沿う transport が誘導する fiber のホモトピー圏間の関手。
方針：単体集合の射である transport に hoFunctor を適用する。
規約：各辺に付随する通常の関手を定義する。
使われ方：Kerodon §5.2.5（Tag 01VT）、ホモトピー transport 表現の構成の入力。 -/
noncomputable def cocartesianTransportHo {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌) :
    hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) ⥤ hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e)) :=
  (hoFunctor.map (cocartesianTransport p e)).toFunctor

/-- 概要：任意の cocartesian transport はホモトピー圏上でも選択した transport と自然同型。
方針：終点 fiber 内の関手同型をホモトピー圏間の自然同型に送る。
規約：底の辺は同じ e に固定する。
使われ方：Kerodon §5.2.5（Tag 01VT）、ホモトピー圏上での選択からの独立性。 -/
lemma IsCocartesianTransport.toHoIso {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌)
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e)}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianTransport p e F) :
    Nonempty ((hoFunctor.map F).toFunctor ≅ cocartesianTransportHo p e) := by
  obtain ⟨i⟩ := hF.functorIso p e (cocartesianTransport_isTransport p e)
  exact ⟨i.toNatIso⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
