module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Path

/-!
概要：cocartesian path の相対始点評価の trivial Kan fibration 性。
方針：零次元では cocartesian lift を選び、正次元では相対 prism を延長する。
規約：新しい頂点を加えない正次元の境界を使い cocartesian 性を保つ。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB）、covariant transport の存在と可縮な選択空間。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：cocartesian fibration の相対始点評価は trivial Kan fibration。
方針：全境界の持ち上げを指定した cocartesian 垂直辺を持つ prism に移す。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Lemma 5.2.2.13（Tag 02RB）、transport の全高次整合性を含む選択。 -/
instance cocartesianPathSource_trivialKanFibration {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource_lift_vertex p b
    exact CommSq.HasLift.mk' { l := g, fac_left := boundary.hom_ext₀, fac_right := hg }
  | succ n =>
      let ev₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
      let r := pullback.fst p ev₀
      let s := pullback.snd p ev₀
      let H := uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p)
      let bH := uncurry (b ≫ s)
      have h₀ : (boundary (n + 1)).ι ≫ (b ≫ r) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
        have hh := congrArg (fun f ↦ f ≫ r) sq.w
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, r, ev₀, Category.assoc,
          pullback.lift_fst] using hh.symm
      have hH : H ≫ p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ bH := by
        apply curry_injective
        rw [curry_natural_right, curry_uncurry, curry_natural_left, curry_uncurry]
        have hh := congrArg (fun f ↦ f ≫ s) sq.w
        simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, s, ev₀, Category.assoc,
          pullback.lift_snd] using hh
      have hb : (b ≫ r) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ bH := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
        dsimp only [r, s, ev₀]
        rw [Category.assoc, pullback.condition, Category.assoc]
      have hC : curry H = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p := curry_uncurry _
      have hhc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prismBoundaryFirstVerticalEdge n)) := by
        let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
          ⟨stdSimplex.obj₀Equiv.symm 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩
        have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
        change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex p ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p).app (Opposite.op ⦋0⦌) x) at hx
        rw [← hC] at hx
        unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex at hx
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at hx
        exact hx
      obtain ⟨F, hF, hF₀, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesian_prism_extend_boundary p n H (b ≫ r) bH h₀ hH hb hhc
      have hc : (boundary (n + 1)).ι ≫ curry F = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p := by
        rw [← curry_natural_left, hF, hC]
      have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex p ((curry F).app (Opposite.op ⦋0⦌) v) := by
        intro v
        let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
          ⟨v, by
            have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
            rw [Equiv.symm_apply_apply] at h
            exact h⟩
        have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
        have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) x
        change (curry F).app (Opposite.op ⦋0⦌) v =
          (a.app (Opposite.op ⦋0⦌) x).val at he
        exact he.symm ▸ hx
      let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsCocartesianPathVertex p) (curry F) hv
      have hg : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p = curry F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
      refine CommSq.HasLift.mk' {
        l := g
        fac_left := ?_
        fac_right := ?_ }
      · have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι; infer_instance
        apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p)).1
        rw [Category.assoc, hg, hc]
      · apply pullback.hom_ext
        · change g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource p ≫ r = b ≫ r
          rw [← Category.assoc, hg]
          simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget, r, ev₀,
            Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval] using hF₀
        · change g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cocartesianPathι p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource p ≫ s = b ≫ s
          rw [← Category.assoc, hg]
          have hh : curry F ≫ (ihom (Δ[1] : SSet.{u})).map p = b ≫ s := by
            rw [← curry_natural_right, hFp, curry_uncurry]
          simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget, s, ev₀,
            Category.assoc,
          pullback.lift_snd] using hh

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
