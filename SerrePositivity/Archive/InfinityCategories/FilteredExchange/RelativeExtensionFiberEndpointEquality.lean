module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointValue

/-!
概要：全延長の終点評価の等式を、元の指定比較の等式へ移す。
方針：終点の等式を消去し、同じ面条件の証明の一意性を使う。
規約：指定比較を再選択しない。使われ方：二辺を固定した全三角形の長辺比較の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 等しい終点評価で読む元の指定比較は厳密に同じ。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_eq_of_endpoint_eq {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j j' : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (hj' : j' ≫ a = SSet.const b)
    (W W' : A ⟶ E) (hp : W ≫ p = a) (hp' : W' ≫ p = a)
    (hs : i ≫ W = v) (hs' : i ≫ W' = v)
    (g g' : C ⟶ vertexFiber p b) (hg : j ≫ W = g ≫ vertexFiberι p b)
    (hg₁ : j ≫ W' = g' ≫ vertexFiberι p b)
    (hg' : j' ≫ W = g ≫ vertexFiberι p b)
    (hg₁' : j' ≫ W' = g' ≫ vertexFiberι p b) (he : j = j') :
    relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W W' hp hp' hs hs' g g' hg hg₁ =
      relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j' b hj'
        W W' hp hp' hs hs' g g' hg' hg₁' := by
  cases he
  rfl

end SerrePositivity.InfinityCategories.F2
