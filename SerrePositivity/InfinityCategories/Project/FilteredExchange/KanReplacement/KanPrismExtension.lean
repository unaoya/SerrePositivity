module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanEquivalencePaths

/-!
概要：Kan 標的の指定部分円柱を、始点を保って全円柱へ延長する。
方針：始点評価の自明 Kan 性を用い、単射なパラメータに沿って持ち上げる。
規約：部分円柱の全単体を厳密に保持する。
使われ方：境界の単射性を確保した有限因子分解の補正。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：Kan 標的の区間関手の始点評価は自明 Kan fibration。
方針：可逆 path の包含同型で元の始点評価の全境界持ち上げを移す。
規約：元の始点評価そのもの。使われ方：部分パラメータの円柱の延長。 -/
lemma intervalEndpoint_zero_trivialKanFibration (X : SSet.{u}) [KanComplex X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app X) := by
  have h : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app X =
      inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 := by
    rw [IsIso.eq_inv_comp]
    rfl
  rw [h]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0))⟩

/-- 概要：指定部分円柱を元の始点を保って全形状へ延長できる。
方針：円柱を curry して始点評価への持ち上げを取り、元の向きへ戻す。
規約：有限性は不要、部分円柱は全時刻で一致。使われ方：有限な境界の補正。 -/
lemma kan_prism_extension {A K X : SSet.{u}} [KanComplex X]
    (i : A ⟶ K) [Mono i] (f : K ⟶ X) (a : A ⊗ (Δ[1] : SSet.{u}) ⟶ X)
    (ha : SSet.ι₀ ≫ a = i ≫ f) :
    ∃ R : K ⊗ (Δ[1] : SSet.{u}) ⟶ X,
      SSet.ι₀ ≫ R = f ∧ (i ▷ (Δ[1] : SSet.{u})) ≫ R = a := by
  have := (intervalEndpoint_zero_trivialKanFibration X).mem i inferInstance
  let a' := (β_ (Δ[1] : SSet.{u}) A).hom ≫ a
  have sq : CommSq (curry a') i ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app X) f := ⟨by
    change curry a' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = i ≫ f
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
    change SSet.ι₀ ≫ a = i ≫ f
    exact ha⟩
  let R := (β_ K (Δ[1] : SSet.{u})).hom ≫ uncurry sq.lift
  refine ⟨R, ?_, ?_⟩
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ uncurry sq.lift = f
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact sq.fac_right
  · dsimp only [R]
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
      ← uncurry_natural_left, sq.fac_left, uncurry_curry]
    dsimp only [a']
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
