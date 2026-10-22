module

public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberEndpointComposition

/-!
概要：同じ実終点の二延長の指定比較が恒等なら、第三の実延長への指定比較は等しい。
方針：元の三比較の合成則から恒等前置比較を消去する。
規約：三つの実延長と指定値を保持。使われ方：二辺固定の長辺普遍比較の選択独立性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ終点の延長間の元の指定比較が恒等なら、同じ第三延長への指定比較は厳密に等しい。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_eq_of_identity {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W₀ W₁ U : A ⟶ E) (h₀ : W₀ ≫ p = a) (h₁ : W₁ ≫ p = a) (hU : U ≫ p = a)
    (s₀ : i ≫ W₀ = v) (s₁ : i ≫ W₁ = v) (sU : i ≫ U = v)
    (g h : C ⟶ vertexFiber p b)
    (j₀ : j ≫ W₀ = g ≫ vertexFiberι p b) (j₁ : j ≫ W₁ = g ≫ vertexFiberι p b)
    (jU : j ≫ U = h ≫ vertexFiberι p b)
    (he : relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W₀ W₁ h₀ h₁ s₀ s₁ g g j₀ j₁ = Iso.refl _) :
    relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W₀ U h₀ hU s₀ sU g h j₀ jU =
    relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W₁ U h₁ hU s₁ sU g h j₁ jU := by
  have hc := relativeExtensionFiberEndpoint_witnessIso_trans p a i hi v hv j b hj
    W₀ W₁ U h₀ h₁ hU s₀ s₁ sU g g h j₀ j₁ jU
  rw [he, Iso.refl_trans] at hc
  exact hc.symm

end SerrePositivity.InfinityCategories.F2
