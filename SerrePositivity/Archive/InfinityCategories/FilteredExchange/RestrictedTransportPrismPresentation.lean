module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportRestrictedPrismComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointDataEquality

/-!
概要：元の輸送比較の係数制限を、同じ実二 prism と同じ底・初期値の表示へ戻す。
方針：実終点は fiber 包含の単射性で回収し、実データの等式による指定値保存を使う。
規約：終点の整合を仮定しない。使われ方：元の実長辺と native 比較の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ底・初期値・実二 prism への表示変更は、指定比較と実両端の値を保持する。 -/
lemma fiberTransportRestrictedPrismComparison_heq_of_prisms {E B K L C : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) (s : C ⟶ K ⊗ L)
    (β : (Δ[1] : SSet.{u}) ⊗ C ⟶ B) (v : C ⟶ E)
    (hv : v ≫ p = prismEndpoint 0 C ≫ β)
    (hb : prismEndpoint 1 C ≫ β = SSet.const b)
    (P₀ P₁ : (Δ[1] : SSet.{u}) ⊗ C ⟶ E)
    (hp₀ : P₀ ≫ p = β) (hp₁ : P₁ ≫ p = β)
    (hs₀ : prismEndpoint 0 C ≫ P₀ = v) (hs₁ : prismEndpoint 0 C ≫ P₁ = v)
    (g₀ g₁ : C ⟶ vertexFiber p b)
    (he₀ : prismEndpoint 1 C ≫ P₀ = g₀ ≫ vertexFiberι p b)
    (he₁ : prismEndpoint 1 C ≫ P₁ = g₁ ≫ vertexFiberι p b)
    (hβ : (Δ[1] ◁ s) ≫ ((Δ[1] ◁ snd K L) ≫ γ) = β)
    (hv' : s ≫ fst K L ≫ f ≫ vertexFiberι p a = v)
    (hP₀ : (Δ[1] ◁ s) ≫ T.prism = P₀)
    (hP₁ : (Δ[1] ◁ s) ≫ U.prism = P₁) :
    HEq ((T.endpointIso p f γ h₁ U).precomp s)
      (relativeExtensionFiberEndpoint_witnessIso p β (prismEndpoint 0 C)
        (prismEndpoint_zero_leftAnodyne C) v hv (prismEndpoint 1 C) b hb
        P₀ P₁ hp₀ hp₁ hs₀ hs₁ g₀ g₁ he₀ he₁) := by
  have hg₀ : s ≫ T.endpoint = g₀ := by
    apply (cancel_mono (vertexFiberι p b)).mp
    rw [Category.assoc, ← T.finish, ← Category.assoc,
      ← prismEndpoint_naturality, Category.assoc, hP₀, he₀]
  have hg₁ : s ≫ U.endpoint = g₁ := by
    apply (cancel_mono (vertexFiberι p b)).mp
    rw [Category.assoc, ← U.finish, ← Category.assoc,
      ← prismEndpoint_naturality, Category.assoc, hP₁, he₁]
  refine (heq_of_eq
    (fiberTransportRestrictedPrismComparison_eq_endpointIso p f γ h₁ T U s).symm).trans ?_
  unfold fiberTransportRestrictedPrismComparison
  exact relativeExtensionFiberEndpoint_witnessIso_heq_of_dataEq p _ β _ _ _ v _ hv _ b _ hb
    _ _ P₀ P₁ _ _ hp₀ hp₁ _ _ hs₀ hs₁ _ _ g₀ g₁ _ _ he₀ he₁ hβ hv' hP₀ hP₁ hg₀ hg₁

end SerrePositivity.InfinityCategories.F2
