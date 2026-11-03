module

public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportIntervalUniversalIdentity

/-!
概要：同じ実辺を持つ二つの表示では、元の指定区間比較も同じ値になる。
方針：実 prism の射影から底の区間族の等式を導き、表示変更を消去する。
規約：端点の一致だけは仮定しない。使われ方：同じ四面体の共有辺の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実辺の二表示は、底の区間族を選び直しても元の指定比較を保持する。 -/
lemma leftFibrationPrism_transportIntervalIso_shared_prism_heq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (c c' : P ⟶ intervalMappingSpace a b) (W W' : Δ[1] ⊗ P ⟶ E)
    (hs : prismEndpoint 0 P ≫ W = f ≫ vertexFiberι p a)
    (hs' : prismEndpoint 0 P ≫ W' = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 P ≫ W = g ≫ vertexFiberι p b)
    (he' : prismEndpoint 1 P ≫ W' = g ≫ vertexFiberι p b)
    (hp : W ≫ p = intervalMappingUncurry c)
    (hp' : W' ≫ p = intervalMappingUncurry c') (hW : W = W') :
    HEq (leftFibrationPrism_transportIntervalIso p f g c W hs he hp)
      (leftFibrationPrism_transportIntervalIso p f g c' W' hs' he' hp') := by
  have hc : c = c' := by
    apply intervalMappingUncurry_injective
    exact hp.symm.trans ((congrArg (fun V => V ≫ p) hW).trans hp')
  cases hc
  cases hW
  rfl

end SerrePositivity.InfinityCategories.F2
