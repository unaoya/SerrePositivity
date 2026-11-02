module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismPostData
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessPost
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointComposition

/-!
概要：元の指定対角比較の後合成と、同じ普遍 prism の像の指定比較は厳密に貼れる。
方針：三つの元の比較を同じ実延長空間の比較へ戻し、その合成則を使う。
規約：比較を選び直さない。使われ方：元の二射の指定評価比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {P E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
  [LeftFibration p] [LeftFibration q] (f : E ⟶ F) (hf : f ≫ q = p)
  {a b : B _⦋0⦌} (x : P ⟶ vertexFiber p a) (y : P ⟶ vertexFiber p b)
  (γ : (Δ[1] : SSet.{u}) ⊗ P ⟶ B)
  (h₀ : prismEndpoint 0 P ≫ γ = SSet.const a)
  (h₁ : prismEndpoint 1 P ≫ γ = SSet.const b)
  (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
  (H₀ : prismEndpoint 0 P ≫ H = x ≫ vertexFiberι p a)
  (H₁ : prismEndpoint 1 P ≫ H = y ≫ vertexFiberι p b) (Hp : H ≫ p = γ)
local notation "c" => intervalMappingCurryOfEndpoints γ h₀ h₁
local notation "k₀" => vertexFiberMap p q f hf a
local notation "k₁" => vertexFiberMap p q f hf b
local notation "U" => diagonalUniversalPrism p x c
local notation "U₀" => diagonalUniversalPrism_start p x c
local notation "U₁" => diagonalUniversalPrism_finish p x c
local notation "Up" => Eq.trans (diagonalUniversalPrism_projection p x c)
  (intervalMappingUncurry_curryOfEndpoints γ h₀ h₁)

/-- 元の実 prism の指定比較と普遍 prism の像の指定比較は、像の元の指定比較へ貼れる。 -/
lemma leftFibrationPrism_diagonalTransportIso_post :
    (leftFibrationPrism_diagonalTransportIso p x y γ h₀ h₁ H H₀ H₁ Hp).postcomp k₁ ≪≫
      leftFibrationPrism_diagonalTransportIso q (x ≫ k₀)
        (diagonalFiberTransport p x c ≫ k₁) γ h₀ h₁ (U ≫ f)
        (diagonalPrismPost_start p q f hf U x U₀)
        (diagonalPrismPost_finish p q f hf U (diagonalFiberTransport p x c) U₁)
        (diagonalPrismPost_projection p q f hf U γ Up) =
      leftFibrationPrism_diagonalTransportIso q (x ≫ k₀) (y ≫ k₁) γ h₀ h₁ (H ≫ f)
        (diagonalPrismPost_start p q f hf H x H₀)
        (diagonalPrismPost_finish p q f hf H y H₁)
        (diagonalPrismPost_projection p q f hf H γ Hp) := by
  rw [leftFibrationPrism_diagonalTransportIso_eq_witness p x γ h₀ y h₁ H H₀ H₁ Hp,
    relativeExtensionFiberEndpoint_witnessIso_post]
  rw [leftFibrationPrism_diagonalTransportIso_eq_witness,
    leftFibrationPrism_diagonalTransportIso_eq_witness]
  exact relativeExtensionFiberEndpoint_witnessIso_trans q γ (prismEndpoint 0 P)
    (prismEndpoint_zero_leftAnodyne P) ((x ≫ vertexFiberι p a) ≫ f)
    (by rw [Category.assoc, hf, diagonalPrismComparison_initial_base p x γ h₀])
    (prismEndpoint 1 P) b h₁ (H ≫ f) (U ≫ f)
    (diagonalUniversalPrism q (x ≫ k₀) c)
    (diagonalPrismPost_projection p q f hf H γ Hp)
    (diagonalPrismPost_projection p q f hf U γ Up)
    (by rw [diagonalUniversalPrism_projection, intervalMappingUncurry_curryOfEndpoints])
    (by rw [← Category.assoc, H₀]) (by rw [← Category.assoc, U₀])
    (by simpa only [Category.assoc, vertexFiberMap_ι] using
      diagonalUniversalPrism_start q (x ≫ k₀) c)
    (y ≫ k₁) (diagonalFiberTransport p x c ≫ k₁)
    (diagonalFiberTransport q (x ≫ k₀) c)
    (diagonalPrismPost_finish p q f hf H y H₁)
    (diagonalPrismPost_finish p q f hf U (diagonalFiberTransport p x c) U₁)
    (diagonalUniversalPrism_finish q (x ≫ k₀) c)

end SerrePositivity.InfinityCategories.F2
