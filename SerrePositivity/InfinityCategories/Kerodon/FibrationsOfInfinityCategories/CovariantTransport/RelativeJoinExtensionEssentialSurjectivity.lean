module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinExtensionFibers
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinQuasicategory

/-!
概要：両端で同値な相対 join の延長の本質的全射性。
方針：指定された始点・終点の比較を延長の fiber の比較に移し、区間の判定を使う。
規約：因子は quasicategory、標的の射影は inner fibration。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、区間上の写像円柱比較の全射性の部分。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration

/-- 概要：両端の比較が同値な区間上の相対 join の延長は本質的全射。
方針：両端の fiber の前合成同値を実際の同値へ移し、全空間の本質的全射性を得る。
規約：垂直辺の cocartesian 性は充満忠実性のための条件であり、この補題には不要。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、fiber ごとの判定との接続。 -/
lemma relativeJoin_extension_isEssentiallySurjective {X Y E : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y)
    (p : E ⟶ (Δ[1] : SSet.{u})) [InnerFibration p]
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) ⟶ E) (hG : G ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y))
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ G = H)
    (g : Y ⟶ E) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 Y) ≫ G = g)
    (z0 : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hz0 : z0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ H)
    (z1 : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hz1 : z1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = g)
    (he0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z0) (he1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence z1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isEssentiallySurjective_over_interval_of_endpoint_fibers
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)) p G hG
  · have h0 := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_extension_zeroFiber_isPrecompositionEquivalence_iff
      f p G hG H hH z0 hz0).mpr he0
    exact h0.isQCatEquivalence.choose.isEssentiallySurjective
  · have h1 := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin_extension_oneFiber_isPrecompositionEquivalence_iff
      f p G hG g hg z1 hz1).mpr he1
    exact h1.isQCatEquivalence.choose.isEssentiallySurjective

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
