module

public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberDataEquality

/-!
概要：元の fiber 終点の指定比較を、実延長と実終点の同じ等式に沿って保持する。
方針：指定した全実データの等式を消去する。
規約：比較の選択は元のものを保持。使われ方：実輸送の右結合比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 底・始点・両実延長・両実終点の表示を等式で変えても指定比較の値を保持する。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_heq_of_dataEq {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b b' : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v v' : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (hv' : v' ≫ p = i ≫ b') (j : C ⟶ A) (z : B _⦋0⦌)
    (hj : j ≫ b = SSet.const z) (hj' : j ≫ b' = SSet.const z)
    (W₀ W₁ W₀' W₁' : A ⟶ E)
    (h₀ : W₀ ≫ p = b) (h₁ : W₁ ≫ p = b)
    (h₀' : W₀' ≫ p = b') (h₁' : W₁' ≫ p = b')
    (hi₀ : i ≫ W₀ = v) (hi₁ : i ≫ W₁ = v)
    (hi₀' : i ≫ W₀' = v') (hi₁' : i ≫ W₁' = v')
    (g₀ g₁ g₀' g₁' : C ⟶ vertexFiber p z)
    (hj₀ : j ≫ W₀ = g₀ ≫ vertexFiberι p z)
    (hj₁ : j ≫ W₁ = g₁ ≫ vertexFiberι p z)
    (hj₀' : j ≫ W₀' = g₀' ≫ vertexFiberι p z)
    (hj₁' : j ≫ W₁' = g₁' ≫ vertexFiberι p z)
    (hb : b = b') (hvv : v = v') (he₀ : W₀ = W₀') (he₁ : W₁ = W₁')
    (hg₀ : g₀ = g₀') (hg₁ : g₁ = g₁') :
    HEq (relativeExtensionFiberEndpoint_witnessIso p b i hi v hv j z hj
      W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁)
      (relativeExtensionFiberEndpoint_witnessIso p b' i hi v' hv' j z hj'
        W₀' W₁' h₀' h₁' hi₀' hi₁' g₀' g₁' hj₀' hj₁') := by
  cases hg₀
  cases hg₁
  exact heq_of_eq (relativeExtensionFiberEndpoint_witnessIso_eq_of_dataEq p b b' i hi
    v v' hv hv' j z hj hj' W₀ W₁ W₀' W₁' h₀ h₁ h₀' h₁' hi₀ hi₁ hi₀' hi₁'
    g₀ g₁ hj₀ hj₁ hj₀' hj₁' hb hvv he₀ he₁)

end SerrePositivity.InfinityCategories.F2
