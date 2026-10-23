module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberComparisonRestriction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberEndpointValue

/-!
概要：元の二つの実延長の指定 fiber 終点比較は、同じ実終点を保つ制限で厳密に一致する。
方針：元の指定比較の値を全延長空間の像へ戻し、同じ制限の自然性を使う。
規約：実終点と指定比較を保持。使われ方：元の二つの prism の結合表示の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実延長の指定 fiber 終点比較は、同じ実終点を保つ制限で厳密に一致する。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_restriction {A D A' D' C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) (i : D ⟶ A) (hi : leftAnodyneExtensions i)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b) (h : A' ⟶ A) (k : D' ⟶ D)
    (i' : D' ⟶ A') (hi' : leftAnodyneExtensions i') (hs : i' ≫ h = k ≫ i)
    (j : C ⟶ A) (j' : C ⟶ A') (hsj : j' ≫ h = j) (z : B _⦋0⦌)
    (hj : j ≫ b = SSet.const z) (W₀ W₁ : A ⟶ E) (h₀ : W₀ ≫ p = b) (h₁ : W₁ ≫ p = b)
    (hi₀ : i ≫ W₀ = v) (hi₁ : i ≫ W₁ = v) (g₀ g₁ : C ⟶ vertexFiber p z)
    (hj₀ : j ≫ W₀ = g₀ ≫ vertexFiberι p z) (hj₁ : j ≫ W₁ = g₁ ≫ vertexFiberι p z) :
    relativeExtensionFiberEndpoint_witnessIso p b i hi v hv j z hj
      W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ =
    relativeExtensionFiberEndpoint_witnessIso p (h ≫ b) i' hi' (k ≫ v)
      (relativeExtensionRestriction_initial_base p b i v hv h k i' hs) j' z
      (relativeExtensionRestriction_endpoint_base b h j j' hsj z hj)
      (h ≫ W₀) (h ≫ W₁) (by rw [Category.assoc, h₀]) (by rw [Category.assoc, h₁])
      (by rw [← Category.assoc, hs, Category.assoc, hi₀])
      (by rw [← Category.assoc, hs, Category.assoc, hi₁]) g₀ g₁
      (by rw [← Category.assoc, hsj, hj₀]) (by rw [← Category.assoc, hsj, hj₁]) := by
  have e₀ := relativeExtensionFiberEndpoint_witnessIso_heq_map p b i hi v hv j z hj
    W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁
  have e₁ := relativeExtensionFiberEndpoint_witnessIso_heq_map p (h ≫ b) i' hi' (k ≫ v)
    (relativeExtensionRestriction_initial_base p b i v hv h k i' hs) j' z
    (relativeExtensionRestriction_endpoint_base b h j j' hsj z hj)
    (h ≫ W₀) (h ≫ W₁) (by rw [Category.assoc, h₀]) (by rw [Category.assoc, h₁])
    (by rw [← Category.assoc, hs, Category.assoc, hi₀])
    (by rw [← Category.assoc, hs, Category.assoc, hi₁]) g₀ g₁
    (by rw [← Category.assoc, hsj, hj₀]) (by rw [← Category.assoc, hsj, hj₁])
  have hc := relativeExtensionFiberComparison_restriction p b i hi v hv h k i' hi' hs
    j j' hsj z hj
    (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W₀, h₀, hi₀⟩)
    (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W₁, h₁, hi₁⟩)
  exact eq_of_heq (e₀.trans (hc.trans e₁.symm))

end SerrePositivity.InfinityCategories.F2
