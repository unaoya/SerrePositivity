module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessPrecomp
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：同じ二実 prism の指定 fiber 比較を、係数射による制限に厳密に移す。
方針：終点の前合成と全 prism 延長空間の制限を合成する。
規約：全実データと指定比較を保持。使われ方：元の普遍三角形比較の係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二実 prism の指定 fiber 比較は、係数全体の再制限と厳密に可換する。 -/
lemma prismFiberWitnessIso_precomp {K L E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (v : K ⟶ E) (hv : v ≫ p = prismEndpoint 0 K ≫ β)
    (z : B _⦋0⦌) (hj : prismEndpoint 1 K ≫ β = SSet.const z)
    (W₀ W₁ : (Δ[1] : SSet.{u}) ⊗ K ⟶ E) (h₀ : W₀ ≫ p = β) (h₁ : W₁ ≫ p = β)
    (hs₀ : prismEndpoint 0 K ≫ W₀ = v) (hs₁ : prismEndpoint 0 K ≫ W₁ = v)
    (g₀ g₁ : K ⟶ vertexFiber p z)
    (he₀ : prismEndpoint 1 K ≫ W₀ = g₀ ≫ vertexFiberι p z)
    (he₁ : prismEndpoint 1 K ≫ W₁ = g₁ ≫ vertexFiberι p z) (r : L ⟶ K) :
    (relativeExtensionFiberEndpoint_witnessIso p β (prismEndpoint 0 K)
      (prismEndpoint_zero_leftAnodyne K) v hv (prismEndpoint 1 K) z hj
      W₀ W₁ h₀ h₁ hs₀ hs₁ g₀ g₁ he₀ he₁).precomp r =
    relativeExtensionFiberEndpoint_witnessIso p ((Δ[1] ◁ r) ≫ β) (prismEndpoint 0 L)
      (prismEndpoint_zero_leftAnodyne L) (r ≫ v)
      (by rw [Category.assoc, hv, ← Category.assoc, ← prismEndpoint_naturality, Category.assoc])
      (prismEndpoint 1 L) z (by
        rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hj, SSet.comp_const])
      ((Δ[1] ◁ r) ≫ W₀) ((Δ[1] ◁ r) ≫ W₁)
      (by rw [Category.assoc, h₀]) (by rw [Category.assoc, h₁])
      (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hs₀])
      (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hs₁])
      (r ≫ g₀) (r ≫ g₁)
      (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, he₀, Category.assoc])
      (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
        he₁, Category.assoc]) := by
  rw [relativeExtensionFiberEndpoint_witnessIso_precomp]
  exact relativeExtensionFiberEndpoint_witnessIso_restriction p β (prismEndpoint 0 K)
    (prismEndpoint_zero_leftAnodyne K) v hv (Δ[1] ◁ r) r (prismEndpoint 0 L)
    (prismEndpoint_zero_leftAnodyne L) (prismEndpoint_naturality 0 r)
    (r ≫ prismEndpoint 1 K) (prismEndpoint 1 L) (prismEndpoint_naturality 1 r)
    z (by rw [Category.assoc, hj, SSet.comp_const])
    W₀ W₁ h₀ h₁ hs₀ hs₁ (r ≫ g₀) (r ≫ g₁)
    (by rw [Category.assoc, he₀, Category.assoc])
    (by rw [Category.assoc, he₁, Category.assoc])

end SerrePositivity.InfinityCategories.F2
