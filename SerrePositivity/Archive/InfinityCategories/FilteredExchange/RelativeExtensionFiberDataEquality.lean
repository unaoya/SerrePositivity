module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointValue

/-!
概要：fiber 終点の指定比較は、底・初期値・実延長の同じ等式による表示変更で保持される。
方針：元の実データの等式を消去し、同じ終点と面の証明の一意性を使う。
規約：指定比較を選び直さない。使われ方：元の prism の結合表示の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の底・初期値・二つの実延長が同じなら、同じ fiber 終点の指定比較も厳密に同じ。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_eq_of_dataEq {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b b' : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v v' : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (hv' : v' ≫ p = i ≫ b') (j : C ⟶ A) (z : B _⦋0⦌)
    (hj : j ≫ b = SSet.const z) (hj' : j ≫ b' = SSet.const z)
    (W₀ W₁ W₀' W₁' : A ⟶ E)
    (h₀ : W₀ ≫ p = b) (h₁ : W₁ ≫ p = b)
    (h₀' : W₀' ≫ p = b') (h₁' : W₁' ≫ p = b')
    (hi₀ : i ≫ W₀ = v) (hi₁ : i ≫ W₁ = v)
    (hi₀' : i ≫ W₀' = v') (hi₁' : i ≫ W₁' = v')
    (g₀ g₁ : C ⟶ vertexFiber p z)
    (hj₀ : j ≫ W₀ = g₀ ≫ vertexFiberι p z)
    (hj₁ : j ≫ W₁ = g₁ ≫ vertexFiberι p z)
    (hj₀' : j ≫ W₀' = g₀ ≫ vertexFiberι p z)
    (hj₁' : j ≫ W₁' = g₁ ≫ vertexFiberι p z)
    (hb : b = b') (hvv : v = v') (he₀ : W₀ = W₀') (he₁ : W₁ = W₁') :
    relativeExtensionFiberEndpoint_witnessIso p b i hi v hv j z hj
        W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ =
      relativeExtensionFiberEndpoint_witnessIso p b' i hi v' hv' j z hj'
        W₀' W₁' h₀' h₁' hi₀' hi₁' g₀ g₁ hj₀' hj₁' := by
  cases hb
  cases hvv
  cases he₀
  cases he₁
  rfl

end SerrePositivity.InfinityCategories.F2
