module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftEndpoint

/-!
概要：底の一本の辺に沿う transport の可縮な選択空間と終点関手。
方針：始点 fiber の包含と底の辺の定値族を固定した lift 空間を使う。
規約：終点は指定された fiber 内で扱う。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport 関手の一意性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：始点 fiber の包含と底の辺の族を同時に指定する図式。
方針：包含と辺の定値族の curry を引き戻しに組み合わせる。
規約：e の始点の fiber 全体がパラメーター。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の選択空間の底。 -/
noncomputable def transportSourceDiagram {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget p :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 1 e))
    (curry (fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e)) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp])

/-- 概要：transport の底の図式の終点は e の終点に定値。
方針：引き戻しの第二射影と curry の評価を計算する。
規約：標的の fiber の底を厳密に固定する。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、終点 fiber 値の関手の構成。 -/
lemma transportSourceDiagram_endpoint {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    transportSourceDiagram p e ≫ pullback.snd p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          SSet.const (B.δ 0 e) := by
  rw [transportSourceDiagram, pullback.lift_snd_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one]

/-- 概要：一本の辺に沿う整合的な cocartesian transport の選択空間。
方針：始点 fiber の包含と底の辺の族を固定した lift の空間を取る。
規約：零単体は始点から終点までの図式全体の選択。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の可縮な選択。 -/
noncomputable def transportChoiceSpace {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpace p (transportSourceDiagram p e)

/-- 概要：transport の選択空間は可縮な Kan 複体。
方針：一般の整合的 lift 空間の可縮性を特殊化する。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の高次の一意性。 -/
lemma transportChoiceSpace_isContractibleKan {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (transportChoiceSpace p e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpace_isContractibleKan p _

/-- 概要：transport の選択から始点 fiber をパラメーターとする cocartesian path の族を得る。
方針：選択空間の頂点と厳密な lift の同値を使う。
規約：返す部分型の条件が始点と底の辺の固定を表す。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、各選択の実際の transport。 -/
noncomputable def transportChoiceLift {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (transportChoiceSpace p e) _⦋0⦌) :
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPath p //
      F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p = transportSourceDiagram p e} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianLiftSpaceVertexEquiv p (transportSourceDiagram p e)).symm x

/-- 概要：transport の選択を終点 fiber 値の関手単体集合へ送る。
方針：終点評価を内部 Hom の fiber に持ち上げ、fiber 値の関手との同型を使う。
規約：始点と終点は e の両端の fiber。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、選択間の自然同型を作る写像。 -/
noncomputable def transportChoiceEndpoint {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    transportChoiceSpace p e ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (transportSourceDiagram p e)) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathEndpoint p 1)) (by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathEndpoint_comp,
      CategoryTheory.Functor.map_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
    change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (transportSourceDiagram p e ≫ pullback.snd p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) = _
    rw [transportSourceDiagram_endpoint]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ihomVertexFiberInverse (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) p (B.δ 0 e)

/-- 概要：選択の終点関手を全空間へ含めると元の lift の終点評価となる。
方針：内部 Hom の fiber 比較の逆関係を使う。
規約：等式は選択空間全体を始域とする射の等式。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、各選択の transport と終点写像の整合性。 -/
lemma transportChoiceEndpoint_comp {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌) :
    transportChoiceEndpoint p e ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 0 e)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (transportSourceDiagram p e)) ≫
          (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathEndpoint p 1) := by
  unfold transportChoiceEndpoint
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.ihomVertexFiberInverse_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 概要：選択された cocartesian lift の終点から得る transport 関手。
方針：path の終点を取り、底の終点の fiber へ持ち上げる。
規約：関手は単体集合の射として与える。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、選択に依存する transport の具体形。 -/
noncomputable def transportAtChoice {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (transportChoiceSpace p e) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (B.δ 0 e)
    ((transportChoiceLift p e x).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathEndpoint p 1) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathEndpoint_comp, ← Category.assoc,
        (transportChoiceLift p e x).property, transportSourceDiagram_endpoint])

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
