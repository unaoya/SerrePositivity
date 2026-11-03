module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantFiberPrism

/-!
概要：実際に定値である任意の区間表示の指定比較を、元の定値輸送比較へ戻す。
方針：同じ実 prism の等式を使い、元の定値比較の逆をそのまま回収する。
規約：指定値を選び直さない。使われ方：実三角形の終辺比較の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実定値 prism の元の区間比較は、元の指定定値輸送比較の逆である。 -/
lemma leftFibrationPrism_transportIntervalIso_constant_eq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a a)
    (hc : intervalMappingUncurry c = SSet.const a) (W : Δ[1] ⊗ P ⟶ E)
    (hs : prismEndpoint 0 P ≫ W = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 P ≫ W = f ≫ vertexFiberι p a)
    (hp : W ≫ p = intervalMappingUncurry c) (hW : W = constantFiberPrism p f) :
    leftFibrationPrism_transportIntervalIso p f f c W hs he hp =
      (diagonalFiberTransport_constantIso p f c hc).symm := by
  rw [diagonalFiberTransport_constantIso_eq_prism, Iso.symm_symm_eq]
  exact leftFibrationPrism_transportIntervalIso_eq_of_prism_eq p f f c W
    (constantFiberPrism p f) hs (constantFiberPrism_endpoint p f 0)
    he (constantFiberPrism_endpoint p f 1) hp ((constantFiberPrism_projection p f).trans hc.symm) hW

end SerrePositivity.InfinityCategories.F2
