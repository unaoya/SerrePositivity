module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PathLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftTransport

/-!
概要：cocartesian fibration の整合的な prism と fiber 間の transport の存在。
方針：相対始点評価の trivial Kan fibration 性から始点の包含を持ち上げる。
規約：全ての垂直辺に cocartesian 性を要求する。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB）、Proposition 5.2.2.8（Tag 01VS）。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：任意のパラメーターを持つ底の prism は cocartesian に持ち上げられる。
方針：相対始点評価の空部分複体に対する rlp を適用して uncurry する。
規約：始点と底の全図式を厳密に固定する。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB） の存在。 -/
lemma cocartesianFibration_lift_prism {A X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (F₀ : A ⟶ X) (b : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hb : F₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ b) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ A ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ F = F₀ ∧ F ≫ p = b ∧
      ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (F.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  let ev₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let c : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget p :=
    pullback.lift F₀ (curry b) (hb.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval b 0).symm)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p) (⊥ : A.Subcomplex).ι
    inferInstance
  have sq : CommSq (Subcomplex.isInitialBot.to (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPath p))
      (⊥ : A.Subcomplex).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p) c :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  let F := uncurry (sq.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p)
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    have h := congrArg (fun f ↦ f ≫ pullback.fst p ev₀) sq.fac_right
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget, c, ev₀,
      Category.assoc, pullback.lift_fst] using h
  · apply curry_injective
    rw [curry_natural_right, curry_uncurry]
    have h := congrArg (fun f ↦ f ≫ pullback.snd p ev₀) sq.fac_right
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget, c, ev₀,
      Category.assoc, pullback.lift_snd] using h
  · intro x
    have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (sq.lift.app (Opposite.op ⦋0⦌) x)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex p
      ((sq.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p).app (Opposite.op ⦋0⦌) x) at hx
    have hC : curry F = sq.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p := curry_uncurry _
    rw [← hC] at hx
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex at hx
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at hx
    exact hx

/-- 概要：cocartesian fibration の辺に沿う fiber 間の transport 関手は存在する。
方針：始点 fiber 全体をパラメーターとする prism を持ち上げ、その終点を fiber に入れる。
規約：底や全空間の quasicategory 性は不要で、全ての垂直辺は cocartesian。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS） の cocartesian fibration の存在。 -/
lemma cocartesianFibration_exists_transport {X B : SSet.{u}} (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (e : B _⦋1⦌) :
    ∃ (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 0 e))
      (H : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ X),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 1 e) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 0 e) ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e ∧
      ∀ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)
  let b := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 1 e) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ b := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_zero]
  obtain ⟨H, hH₀, hHp, hHc⟩ := cocartesianFibration_lift_prism p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 1 e)) b hb
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) ≫ p = SSet.const (B.δ 0 e) := by
    rw [Category.assoc, hHp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one]
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (B.δ 0 e) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) ht
  exact ⟨F, H, hH₀, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _).symm, hHp,
    hHc⟩


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
