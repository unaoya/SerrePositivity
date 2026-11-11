module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanHomotopyMappedComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPairPresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberSourceVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.DiagonalFiberTransportSourceIso

/-!
概要：元の始点同型の対角輸送は、同じ関手空間の作用による指定同型の像。
方針：元の選択代表辺の像を実際の輸送ホモトピーの辺に一致させる。
規約：元の sourceIso の選択を保持。使われ方：合成四角形の指定三因子の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の始点同型の輸送は、元の全区間作用の同じ一つの指定像に等しい。 -/
lemma diagonalFiberTransport_sourceIso_heq_action {P E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g) (c : P ⟶ intervalMappingSpace a b) :
    HEq (diagonalFiberTransport_sourceIso p e c)
      (VertexIso.map e (functorPairRight c ≫
        (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint)) := by
  haveI : KanComplex (vertexFiber p a) := vertexFiber_kanComplex_of_leftFibration p a
  haveI : KanComplex (vertexFiber p b) := vertexFiber_kanComplex_of_leftFibration p b
  unfold diagonalFiberTransport_sourceIso
  apply functorIsoOfSimplicialHomotopy_heq_map_of_edge e
    (functorPairRight c ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint)
  change SSet.yonedaEquiv (curry
    (lift e.simplicialHomotopy.h (fst P (Δ[1] : SSet.{u}) ≫ c) ≫
      (parametrizedFiberTransportFamily p a b).endpoint)) =
    (functorPairRight c ≫ (ihom P).map
      (parametrizedFiberTransportFamily p a b).endpoint).app (Opposite.op ⦋1⦌)
        (FunctorIso.edge e).edge
  apply (SSet.yonedaEquiv (X := (ihom P).obj (vertexFiber p b)) (n := ⦋1⦌)).symm.injective
  rw [Equiv.symm_apply_apply, ← SSet.yonedaEquiv_symm_comp]
  apply uncurry_injective
  rw [uncurry_curry]
  change _ = uncurry ((SSet.yonedaEquiv.symm (FunctorIso.edge e).edge ≫
    functorPairRight c) ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint)
  rw [uncurry_natural_right]
  congr 1

end SerrePositivity.InfinityCategories.F2
