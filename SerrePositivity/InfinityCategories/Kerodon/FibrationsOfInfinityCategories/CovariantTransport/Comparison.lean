module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Choices

/-!
概要：transport の二つの整合的な選択の比較。
方針：可縮な選択空間から終点 fiber 値の関手単体集合へ写す。
規約：同型は終点 fiber 内の関手の同型である。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の一意性とホモトピー圏への移行。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：選択から復元した lift の関手頂点は元の選択の値。
方針：関手頂点の同値の逆関係を使う。
規約：選択は内部 Hom の fiber の零単体。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、終点関手の具体的計算。 -/
lemma transportChoiceLift_vertex {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceSpace p e) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceLift p e x).val = x.val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _

/-- 概要：選択空間からの終点写像の頂点は、選択から作った transport 関手を表す。
方針：終点 fiber の包含で後合成して両者を比較する。
規約：終点写像は単体集合の射として全次数を保つ。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、選択空間と実際の transport の接続。 -/
lemma transportAtChoice_vertex {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceSpace p e) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceEndpoint p e).app (Opposite.op ⦋0⦌) x := by
  have : Mono ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 0 e))) :=
    inferInstance
  have hm : Function.Injective
      (((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 0 e))).app
        (Opposite.op ⦋0⦌)) := (mono_iff_injective _).1 inferInstance
  apply hm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 0 e)) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  have hx := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceEndpoint_comp p e) (Opposite.op ⦋0⦌)) x
  change (((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 0 e))).app
    (Opposite.op ⦋0⦌)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceEndpoint p e).app (Opposite.op ⦋0⦌) x) =
      (((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathEndpoint p 1)).app
        (Opposite.op ⦋0⦌)) x.val at hx
  rw [← transportChoiceLift_vertex p e x] at hx
  exact hx.symm

/-- 概要：選択から作った transport は cocartesian な prism で実現される。
方針：選択の lift を uncurry し、相対始点評価の二つの成分を読む。
規約：始点と底の辺の族は厳密に指定したもの。
使われ方：Kerodon Definition 5.2.2.4（Tag 019N）、Proposition 5.2.2.8（Tag 01VS） の transport の証人。 -/
lemma transportAtChoice_witness {X B : SSet.{u}} (p : X ⟶ B) (e : B _⦋1⦌)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceSpace p e) _⦋0⦌) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e) ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 1 e) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (B.δ 0 e) ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e ∧
      ∀ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (B.δ 1 e)) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)) := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceLift p e x
  let H := uncurry (a.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p)
  have hC : curry H = a.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p := curry_uncurry _
  let ev := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
    have h := congrArg (fun f ↦ f ≫ pullback.fst p ev) a.property
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportSourceDiagram, ev,
      Category.assoc, pullback.lift_fst] using h
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathEndpoint, Category.assoc]
    rfl
  · apply curry_injective
    rw [curry_natural_right, hC]
    have h := congrArg (fun f ↦ f ≫ pullback.snd p ev) a.property
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportSourceDiagram, ev,
      Category.assoc, pullback.lift_snd] using h
  · intro v
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.val.app (Opposite.op ⦋0⦌) v)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex p ((a.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p).app (Opposite.op ⦋0⦌) v) at hv
    rw [← hC] at hv
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex at hv
    rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at hv

/-- 概要：二つの整合的な選択から得る transport 関手は終点 fiber 内で同型。
方針：可縮な選択空間の頂点同型を終点写像で送る。
規約：同型は FunctorIso、すなわち関手単体集合のホモトピー圏の同型。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の選択からの独立性。 -/
noncomputable def transportAtChoiceIso {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (e : B _⦋1⦌) (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceSpace p e) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e x) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e y) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportAtChoice p e y))
  rw [transportAtChoice_vertex, transportAtChoice_vertex]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceSpace_isContractibleKan p e).vertexIso x y).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.transportChoiceEndpoint p e)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
