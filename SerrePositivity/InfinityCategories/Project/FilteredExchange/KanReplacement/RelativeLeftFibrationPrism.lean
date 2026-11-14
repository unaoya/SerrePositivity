module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPath

/-!
概要：left fibration の prism を部分パラメータ上の指定を保って持ち上げる。
方針：始点と底の区間族を記録する相対評価の trivial Kan fibration 性を使う。
規約：始点と底の全円柱と指定した部分円柱を厳密に固定する。
使われ方：coherent な filtered 図式の有限検出の境界固定版。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：始点・底・部分 prism を同時に指定した持ち上げは存在する。
方針：相対始点評価への可換四角形を作り、任意の単射の持ち上げを使う。
規約：部分パラメータと全パラメータに有限性を要求しない。使われ方：相対 fiber 輸送。 -/
lemma leftFibration_lift_prism_relative {A K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : A ⟶ K) [Mono i]
    (f : K ⟶ E) (b : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (a : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hb : f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ b)
    (ha₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ a = i ≫ f)
    (hap : a ≫ p = (Δ[1] ◁ i) ≫ b) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ K ⟶ E,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R = f ∧ (Δ[1] ◁ i) ≫ R = a ∧ R ≫ p = b := by
  let ev₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSourceTarget p :=
    pullback.lift f (curry b) (hb.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval b 0).symm)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource p) i inferInstance
  have sq : CommSq (curry a) i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource p) c := by
    constructor
    apply pullback.hom_ext
    · change curry a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource p ≫ pullback.fst p ev₀ =
        i ≫ c ≫ pullback.fst p ev₀
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, c, ev₀, pullback.lift_fst,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ha₀]
    · change curry a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource p ≫ pullback.snd p ev₀ =
        i ≫ c ≫ pullback.snd p ev₀
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, c, ev₀, pullback.lift_snd]
      rw [← curry_natural_right, hap, curry_natural_left]
  let R := uncurry sq.lift
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    have h := congrArg (fun q ↦ q ≫ pullback.fst p ev₀) sq.fac_right
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, c, ev₀, Category.assoc, pullback.lift_fst] using h
  · apply curry_injective
    rw [curry_natural_left, curry_uncurry, sq.fac_left]
  · apply curry_injective
    rw [curry_natural_right, curry_uncurry]
    have h := congrArg (fun q ↦ q ≫ pullback.snd p ev₀) sq.fac_right
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.relativeEdgeSource, c, ev₀, Category.assoc, pullback.lift_snd] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
