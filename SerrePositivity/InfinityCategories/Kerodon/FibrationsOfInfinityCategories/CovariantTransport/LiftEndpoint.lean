module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：整合的な cocartesian lift の終点を、底の図式を固定した関手として取り出す。
方針：相対始点評価との可換性により内部 Hom の fiber へ写す。
規約：比較は全空間内だけでなく指定された底の図式上で行う。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport 関手の一意性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：cocartesian path の指定した端点を取る。
方針：区間からの関手への包含の後で頂点を評価する。
規約：i=0 が始点、i=1 が終点。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の終点関手。 -/
def cocartesianPathEndpoint {X B : SSet.{u}} (p : X ⟶ B) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPath p ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i)

/-- 概要：cocartesian path の終点の底は元の底の辺の終点。
方針：内部 Hom の後合成と頂点評価の自然性を使う。
規約：相対始点評価の第二成分が底の辺の族。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、終点 fiber 内での比較。 -/
lemma cocartesianPathEndpoint_comp {X B : SSet.{u}} (p : X ⟶ B) :
    cocartesianPathEndpoint p 1 ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p ≫
      pullback.snd p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  simp only [cocartesianPathEndpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource,
    Category.assoc, pullback.lift_snd_assoc]
  rfl

/-- 概要：整合的な lift の選択空間から、終点の図式上の関手の fiber への写像。
方針：終点評価で後合成し、底の図式が固定されることを確認する。
規約：c は始点と底の辺の族を同時に指定する。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の比較の基礎。 -/
noncomputable def cocartesianLiftSpaceEndpoint {A X B : SSet.{u}} (p : X ⟶ B)
    (c : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpace p c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom A).map p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (c ≫ pullback.snd p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c) ≫
      (ihom A).map (cocartesianPathEndpoint p 1)) (by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, cocartesianPathEndpoint_comp,
      CategoryTheory.Functor.map_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
    rfl)

/-- 概要：可縮な Kan 複体の任意の二頂点はホモトピー圏で同型。
方針：終対象性で辺を取り、Kan 性でその類の可逆性を示す。
規約：頂点の等式は要求しない。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、可縮な lift 空間からの transport の比較。 -/
noncomputable def IsContractibleKan.vertexIso {K : SSet.{u}} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K)
    (x y : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y := by
  have : KanComplex K := h.kanComplex
  let e := Classical.choice ((h.isTerminalVertex y).nonempty_edge x)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj K) _
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsContractibleKan (vertexIso)


/-- 概要：二つの整合的な lift の終点は固定した底の図式上で同型。
方針：可縮な選択空間の二頂点の同型を終点の射で写す。
規約：同型は後合成の内部 Hom の fiber 内で得られる。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、終点 fiber での transport の一意性。 -/
noncomputable def cocartesianLiftSpaceEndpointIso {A X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (c : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget p)
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpace p c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cocartesianLiftSpaceEndpoint p c).app (Opposite.op ⦋0⦌) x)
      ((cocartesianLiftSpaceEndpoint p c).app (Opposite.op ⦋0⦌) y) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpace_isContractibleKan p c).vertexIso x y).map
    (cocartesianLiftSpaceEndpoint p c)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
