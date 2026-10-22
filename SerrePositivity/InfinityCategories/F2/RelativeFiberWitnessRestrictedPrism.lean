module

public import SerrePositivity.InfinityCategories.F2.FiberTransportRestrictedPrismComparison
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionFiberEndpointDataEquality

/-!
概要：元の実二 prism と輸送族の係数制限が一致すれば、その指定 fiber 比較も一致する。
方針：底・始点・両終点を同じ実 prism から回収し、指定比較の表示変更を使う。
規約：端点等式は実射から計算する。使われ方：元の三角形の最後辺と一点輸送の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実 prism の一致は、実両端を含めた同じ指定比較の一致を与える。 -/
lemma relativeFiberWitness_heq_restrictedPrism {E B K L C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) (s : C ⟶ K ⊗ L)
    (β : (Δ[1] : SSet.{u}) ⊗ C ⟶ B) (v : C ⟶ E)
    (hv : v ≫ p = prismEndpoint 0 C ≫ β)
    (hj : prismEndpoint 1 C ≫ β = SSet.const b)
    (W₀ W₁ : (Δ[1] : SSet.{u}) ⊗ C ⟶ E)
    (h₀ : W₀ ≫ p = β) (h₁' : W₁ ≫ p = β)
    (hi₀ : prismEndpoint 0 C ≫ W₀ = v) (hi₁ : prismEndpoint 0 C ≫ W₁ = v)
    (g₀ g₁ : C ⟶ vertexFiber p b)
    (hj₀ : prismEndpoint 1 C ≫ W₀ = g₀ ≫ vertexFiberι p b)
    (hj₁ : prismEndpoint 1 C ≫ W₁ = g₁ ≫ vertexFiberι p b)
    (he₀ : W₀ = (Δ[1] ◁ s) ≫ T.prism) (he₁ : W₁ = (Δ[1] ◁ s) ≫ U.prism) :
    HEq (relativeExtensionFiberEndpoint_witnessIso p β (prismEndpoint 0 C)
      (prismEndpoint_zero_leftAnodyne C) v hv (prismEndpoint 1 C) b hj
      W₀ W₁ h₀ h₁' hi₀ hi₁ g₀ g₁ hj₀ hj₁)
      (fiberTransportRestrictedPrismComparison p f γ h₁ T U s) := by
  have hb : β = (Δ[1] ◁ s) ≫ (Δ[1] ◁ snd K L) ≫ γ := by
    rw [← h₀, he₀, Category.assoc, T.over_base]
  have hvv : v = s ≫ fst K L ≫ f ≫ vertexFiberι p a := by
    rw [← hi₀, he₀, ← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start]
  have hg₀ : g₀ = s ≫ T.endpoint := by
    apply vertexFiber_hom_ext p b
    rw [← hj₀, he₀, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
      T.finish, Category.assoc]
  have hg₁ : g₁ = s ≫ U.endpoint := by
    apply vertexFiber_hom_ext p b
    rw [← hj₁, he₁, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
      U.finish, Category.assoc]
  exact relativeExtensionFiberEndpoint_witnessIso_heq_of_dataEq p β _ (prismEndpoint 0 C)
    (prismEndpoint_zero_leftAnodyne C) v _ hv _ (prismEndpoint 1 C) b hj _
    W₀ W₁ _ _ h₀ h₁' _ _ hi₀ hi₁ _ _ g₀ g₁ _ _ hj₀ hj₁ _ _
    hb hvv he₀ he₁ hg₀ hg₁

end SerrePositivity.InfinityCategories.F2
