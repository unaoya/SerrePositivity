module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionPrismEndpointWitness
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismSpecifiedNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismNativeSourceIso

/-!
概要：全延長の同じ比較の辺制限は、全図式の両端比較と sourceIso の正方形を満たす。
方針：指定対角比較の自然性の両端像を、元の全延長の指定終点比較へ戻す。
規約：元の全実延長・指定比較を保持。使われ方：四角形の三辺の同じ自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {D I E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (β : D ⟶ B)
  (i : I ⟶ D) (hi : leftAnodyneExtensions i) (v : I ⟶ E) (hv : v ≫ p = i ≫ β)
  (W W' : D ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v) (r : (Δ[1] : SSet.{u}) ⊗ A ⟶ D)
  (a b : B _⦋0⦌)
  (ha : (prismEndpoint 0 A ≫ r) ≫ β = SSet.const a)
  (hb : (prismEndpoint 1 A ≫ r) ≫ β = SSet.const b)
  (f f' : A ⟶ vertexFiber p a) (g g' : A ⟶ vertexFiber p b)
  (hs : (prismEndpoint 0 A ≫ r) ≫ W = f ≫ vertexFiberι p a)
  (hs' : (prismEndpoint 0 A ≫ r) ≫ W' = f' ≫ vertexFiberι p a)
  (he : (prismEndpoint 1 A ≫ r) ≫ W = g ≫ vertexFiberι p b)
  (he' : (prismEndpoint 1 A ≫ r) ≫ W' = g' ≫ vertexFiberι p b)
local notation "h₀" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 0 A) r β)) ha
local notation "h₁" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 1 A) r β)) hb
local notation "s₀" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 0 A) r W)) hs
local notation "s₀'" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 0 A) r W')) hs'
local notation "s₁" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 1 A) r W)) he
local notation "s₁'" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 1 A) r W')) he'
local notation "hp" => Eq.trans (Category.assoc r W p) (congrArg (fun t ↦ r ≫ t) hW)
local notation "hp'" => Eq.trans (Category.assoc r W' p) (congrArg (fun t ↦ r ≫ t) hW')
local notation "η" => relativeExtensionPrismRestrictionIso p β i hi v hv
  W W' hW hW' hWi hWi' r
local notation "J₀" => relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
  (prismEndpoint 0 A ≫ r) a ha W W' hW hW' hWi hWi' f f' hs hs'
local notation "J₁" => relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
  (prismEndpoint 1 A ≫ r) b hb W W' hW hW' hWi hWi' g g' he he'

/-- 元の全延長の両端比較と、同じ辺の指定対角比較は sourceIso の正方形を満たす。 -/
lemma relativeExtensionPrism_source_square :
    J₁ ≪≫ leftFibrationPrism_diagonalTransportIso p f' g' (r ≫ β) h₀ h₁
      (r ≫ W') s₀' s₁' hp' =
      leftFibrationPrism_diagonalTransportIso p f g (r ≫ β) h₀ h₁
        (r ≫ W) s₀ s₁ hp ≪≫
        diagonalFiberTransport_sourceIso p J₀ (intervalMappingCurryOfEndpoints (r ≫ β) h₀ h₁) := by
  have h := relativePrismSpecified_naturality p (r ≫ β) a b h₀ h₁
    (r ≫ W) (r ≫ W') hp hp' f f' g g' s₀ s₀' s₁ s₁' η
  have hn := relativePrismNativeEndpointIso_heq_sourceIso p (r ≫ β) a b h₀ h₁
    (r ≫ W) (r ≫ W') hp hp' f f' s₀ s₀' η
  rw [eq_of_heq hn] at h
  rw [relativeExtensionPrism_initial_eq_witness,
    relativeExtensionPrism_actual_eq_witness] at h
  exact h

end SerrePositivity.InfinityCategories.F2
