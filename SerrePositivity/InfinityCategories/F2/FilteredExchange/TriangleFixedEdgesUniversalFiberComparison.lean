module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TriangleFixedEdgesPointFiberIdentity
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberWitnessIdentityCancellation

/-!
概要：二辺固定の全三角形から同じ長辺普遍 prism への指定比較は厳密に一致する。
方針：元の長辺間の指定比較の恒等性を、同じ三実 prism の合成則で消去する。
規約：実底・初期値・指定比較を保持。使われ方：全長辺比較成分の内部選択の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 二辺固定の全三角形から同じ長辺普遍 prism への指定比較は、値まで厳密に等しい。 -/
lemma triangleFixedEdgesUniversalFiberComparison_eq {A E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (β : (Δ[2] : SSet.{u}) ⊗ A ⟶ B)
    (v : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hv : v ≫ p = (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ β)
    (z : B _⦋0⦌)
    (hj : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ β = SSet.const z)
    (W₀ W₁ : (Δ[2] : SSet.{u}) ⊗ A ⟶ E) (h₀ : W₀ ≫ p = β) (h₁ : W₁ ≫ p = β)
    (hi₀ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₀ = v)
    (hi₁ : (stdSimplex.δ (2 : Fin 3) ▷ A) ≫ W₁ = v) (g : A ⟶ vertexFiber p z)
    (hj₀ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₀ = g ≫ vertexFiberι p z)
    (hj₁ : (prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A)) ≫ W₁ = g ≫ vertexFiberι p z)
    (he : (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ W₀ = (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ W₁)
    (c : (Δ[1] : SSet.{u}) ⊗ A ⟶ B) (hc : c = (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ β)
    (u : A ⟶ E) (hu : u = prismEndpoint 0 A ≫ v)
    (hU : u ≫ p = prismEndpoint 0 A ≫ c) (hJ : prismEndpoint 1 A ≫ c = SSet.const z)
    (hp₀ : ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₀) ≫ p = c)
    (hp₁ : ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₁) ≫ p = c)
    (hs₀ : prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₀ = u)
    (hs₁ : prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₁ = u)
    (U : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hUV : U ≫ p = c)
    (sUV : prismEndpoint 0 A ≫ U = u) (k : A ⟶ vertexFiber p z)
    (jUV : prismEndpoint 1 A ≫ U = k ≫ vertexFiberι p z) :
    relativeExtensionFiberEndpoint_witnessIso p c (prismEndpoint 0 A)
      (prismEndpoint_zero_leftAnodyne A) u hU (prismEndpoint 1 A) z hJ
      ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₀) U hp₀ hUV hs₀ sUV g k
      (by simpa only [Category.assoc] using hj₀) jUV =
    relativeExtensionFiberEndpoint_witnessIso p c (prismEndpoint 0 A)
      (prismEndpoint_zero_leftAnodyne A) u hU (prismEndpoint 1 A) z hJ
      ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₁) U hp₁ hUV hs₁ sUV g k
      (by simpa only [Category.assoc] using hj₁) jUV := by
  exact relativeExtensionFiberEndpoint_witnessIso_eq_of_identity p c (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) u hU (prismEndpoint 1 A) z hJ
    ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₀) ((stdSimplex.δ (1 : Fin 3) ▷ A) ≫ W₁) U
    hp₀ hp₁ hUV hs₀ hs₁ sUV g k
    (by simpa only [Category.assoc] using hj₀)
    (by simpa only [Category.assoc] using hj₁) jUV
    (triangleFixedEdgesPointFiberComparison_eq_refl p β v hv z hj W₀ W₁ h₀ h₁ hi₀ hi₁
      g hj₀ hj₁ he c hc u hu hU hJ hp₀ hp₁ hs₀ hs₁)

end SerrePositivity.InfinityCategories.F2
