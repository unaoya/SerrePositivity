module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionIntervalSourceSquare
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionInitialEndpointIdentity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoIdentity

/-!
概要：固定初期図式内に始点を持つ辺の、元の指定比較の自然性。
方針：一般の始点正方形から初期図式上の恒等比較を消去する。
規約：元の指定比較を保持。使われ方：持ち上げ四角形の左右辺の自然性。
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
  (f : A ⟶ vertexFiber p a) (g g' : A ⟶ vertexFiber p b)
  (hs : (prismEndpoint 0 A ≫ r) ≫ W = f ≫ vertexFiberι p a)
  (hs' : (prismEndpoint 0 A ≫ r) ≫ W' = f ≫ vertexFiberι p a)
  (he : (prismEndpoint 1 A ≫ r) ≫ W = g ≫ vertexFiberι p b)
  (he' : (prismEndpoint 1 A ≫ r) ≫ W' = g' ≫ vertexFiberι p b)
  (c : A ⟶ intervalMappingSpace a b) (hc : r ≫ β = intervalMappingUncurry c)
local notation "h₀" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 0 A) r β)) ha
local notation "h₁" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 1 A) r β)) hb
local notation "s₀" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 0 A) r W)) hs
local notation "s₀'" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 0 A) r W')) hs'
local notation "s₁" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 1 A) r W)) he
local notation "s₁'" => Eq.trans (Eq.symm (Category.assoc (prismEndpoint 1 A) r W')) he'
local notation "hp" => Eq.trans (Category.assoc r W p) (congrArg (fun t ↦ r ≫ t) hW)
local notation "hp'" => Eq.trans (Category.assoc r W' p) (congrArg (fun t ↦ r ≫ t) hW')
local notation "J₀" => relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
  (prismEndpoint 0 A ≫ r) a ha W W' hW hW' hWi hWi' f f hs hs'
local notation "J₁" => relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
  (prismEndpoint 1 A ≫ r) b hb W W' hW hW' hWi hWi' g g' he he'


include ha in
/-- 始点が固定初期図式内にある辺では、始点像を恒等として消去できる。 -/
lemma relativeExtensionInterval_source_square_of_initial
    (k : A ⟶ I) (hk : k ≫ i = prismEndpoint 0 A ≫ r) :
    J₁ ≪≫ leftFibrationPrism_transportIntervalIso p f g' c (r ≫ W') s₀' s₁' ((hp').trans hc) =
      leftFibrationPrism_transportIntervalIso p f g c (r ≫ W) s₀ s₁ ((hp).trans hc) := by
  have h := relativeExtensionInterval_source_square p β i hi v hv W W' hW hW' hWi hWi'
    r a b ha hb f f g g' hs hs' he he' c hc
  have hid := relativeExtensionFiberEndpoint_witnessIso_eq_refl_of_initial p β i hi v hv
    (prismEndpoint 0 A ≫ r) k hk a ha W W' hW hW' hWi hWi' f hs hs'
  rw [hid, diagonalFiberTransport_sourceIso_refl, Iso.trans_refl] at h
  exact h

end SerrePositivity.InfinityCategories.F2
