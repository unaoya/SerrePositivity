module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTransportPrecomp
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareUniversalSource

/-!
概要：元の定値輸送比較を、同じ普遍始点の定値比較の制限として保持する。
方針：始点 fiber と係数の直積上で構成し、元の始点のグラフへ制限する。
規約：元の定値比較の選択を保持。使われ方：定値輸送比較の始点自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の普遍始点での定値比較のグラフ制限は、元の始点での同じ指定値。 -/
lemma diagonalFiberTransport_constantIso_universal_precomp_heq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a a)
    (hc : intervalMappingUncurry c = SSet.const a)
    (hU : intervalMappingUncurry (snd (vertexFiber p a) P ≫ c) = SSet.const a) :
    HEq ((diagonalFiberTransport_constantIso p (fst (vertexFiber p a) P)
      (snd (vertexFiber p a) P ≫ c) hU).precomp (lift f (𝟙 P)))
      (diagonalFiberTransport_constantIso p f c hc) := by
  have hq := intervalMappingUncurry_precomp_constant (snd (vertexFiber p a) P ≫ c) hU
    (lift f (𝟙 P))
  have h := diagonalFiberTransport_constantIso_precomp_heq p (fst (vertexFiber p a) P)
    (snd (vertexFiber p a) P ≫ c) hU (lift f (𝟙 P)) hq
  exact h.trans (diagonalFiberTransport_constantIso_heq_of_data p _ f _ c hq hc
    (lift_fst f (𝟙 P)) (by rw [← Category.assoc, lift_snd, Category.id_comp]))

end SerrePositivity.InfinityCategories.F2
