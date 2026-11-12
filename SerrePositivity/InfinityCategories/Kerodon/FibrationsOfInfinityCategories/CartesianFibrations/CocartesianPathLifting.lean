module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPathVertices

/-!
概要：cocartesian な path の始点と基底への射の trivial Kan fibration 性。
方針：零次元は辺の持ち上げ、正次元は cocartesian な prism の相対充填を使う。
規約：元・標的の quasicategory 性は仮定しない。
使われ方：Kerodon §5.1.4（Tag 01U9）・§7.1.5（Tag 02WE） の指定部分を固定した coherent な輸送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：cocartesian な path から始点と基底の path への射は trivial Kan fibration。
方針：境界の path を prism に直して始点の単体と共に持ち上げ、全部分複体へ戻す。
規約：cocartesian fibration の仮定のみで quasicategory 性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9）・§7.1.5（Tag 02WE） の輸送の coherent な選択。 -/
instance cocartesianPathSpaceSource_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceSource p) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary]
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceSource_surjective p (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm t
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, ht]
  | succ n =>
    let evB := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    let H := uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p)
    let β := uncurry (b ≫ pullback.snd p evB)
    let F₀ := b ≫ pullback.fst p evB
    have hC : curry H = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p := curry_uncurry _
    have h₀ : (boundary (n + 1)).ι ≫ F₀ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hC]
      have hh := congrArg (fun t ↦ t ≫ pullback.fst p evB) sq.w
      dsimp only [evB] at hh
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceSource_fst, F₀] using hh.symm
    have hHp : H ≫ p = (Δ[1] ◁ (boundary (n + 1)).ι) ≫ β := by
      have hh := congrArg (fun t ↦ t ≫ pullback.snd p evB) sq.w
      dsimp only [evB] at hh
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceSource_snd] at hh
      rw [← Category.assoc a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p)] at hh
      have hu := congrArg uncurry hh
      rw [uncurry_natural_right, uncurry_natural_left] at hu
      exact hu
    have hF₀p : F₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ β := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
      dsimp [F₀, β]
      rw [curry_uncurry, Category.assoc, pullback.condition]
      simp only [evB, Category.assoc]
    have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (H.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.prismBoundaryFirstVerticalEdge n))) := by
      let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
        ⟨stdSimplex.obj₀Equiv.symm 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩
      have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianHornPathVertex p ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p).app (Opposite.op ⦋0⦌) x) at hx
      rw [← hC] at hx
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianHornPathVertex at hx
      change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
        ((curry H).app (Opposite.op ⦋0⦌) x))) at hx
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry] at hx
      exact hx
    obtain ⟨F, hF, hF₀, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.prism_lift_boundary_with_endpoint p n H F₀ β h₀ hHp hF₀p hH
    have hc : (boundary (n + 1)).ι ≫ curry F = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p := by
      rw [← curry_natural_left, hF, hC]
    have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianHornPathVertex p ((curry F).app (Opposite.op ⦋0⦌) v) := by
      intro v
      let x : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
        ⟨v, by
          have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
          rw [Equiv.symm_apply_apply] at h
          exact h⟩
      have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hc (Opposite.op ⦋0⦌)) x
      change (curry F).app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) x).val at he
      exact he.symm ▸ hx
    let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianHornPathVertex p) (curry F) hv
    have hg : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p = curry F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · haveI : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι; infer_instance
      apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceι p)).1
      rw [Category.assoc, hg, hc]
    · apply pullback.hom_ext
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceSource_fst]
        rw [← Category.assoc, hg, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, hF₀]
      · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianPathSpaceSource_snd]
        rw [← Category.assoc, hg]
        apply uncurry_injective
        rw [uncurry_natural_right, uncurry_curry, hFp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
