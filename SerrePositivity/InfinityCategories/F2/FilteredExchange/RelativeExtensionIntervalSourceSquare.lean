module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionPrismSourceSquare
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportIntervalComparisonPresentation

/-!
概要：全延長の両端比較と、元の区間表示による指定比較の sourceIso 正方形。
方針：同じ実 prism の底と native 頂点を揃え、指定値の自然性正方形を移す。
規約：元の区間比較を保持。使われ方：持ち上げ四角形の三辺比較の照合。
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
  (prismEndpoint 0 A ≫ r) a ha W W' hW hW' hWi hWi' f f' hs hs'
local notation "J₁" => relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
  (prismEndpoint 1 A ≫ r) b hb W W' hW hW' hWi hWi' g g' he he'

/-- 元の区間比較を保った全延長の指定自然性正方形。 -/
lemma relativeExtensionInterval_source_square :
    J₁ ≪≫ leftFibrationPrism_transportIntervalIso p f' g' c (r ≫ W') s₀' s₁' ((hp').trans hc) =
      leftFibrationPrism_transportIntervalIso p f g c (r ≫ W) s₀ s₁ ((hp).trans hc) ≪≫
        diagonalFiberTransport_sourceIso p J₀ c := by
  have h := relativeExtensionPrism_source_square p β i hi v hv W W' hW hW' hWi hWi'
    r a b ha hb f f' g g' hs hs' he he'
  have hvcurve : intervalMappingCurryOfEndpoints (r ≫ β) h₀ h₁ = c := by
    apply intervalMappingUncurry_injective
    rw [intervalMappingUncurry_curryOfEndpoints, hc]
  have changeCurve {c₀ c₁ : A ⟶ intervalMappingSpace a b} (h : c₀ = c₁) :
      HEq (diagonalFiberTransport_sourceIso p J₀ c₀)
        (diagonalFiberTransport_sourceIso p J₀ c₁) := by cases h; rfl
  exact vertexIso_square_of_heq _ _ _ _ J₁
    (leftFibrationPrism_transportIntervalIso p f' g' c (r ≫ W') s₀' s₁' ((hp').trans hc))
    (leftFibrationPrism_transportIntervalIso p f g c (r ≫ W) s₀ s₁ ((hp).trans hc))
    (diagonalFiberTransport_sourceIso p J₀ c) rfl rfl
    (congrArg (fun t ↦ functorVertex (diagonalFiberTransport p f t)) hvcurve)
    (congrArg (fun t ↦ functorVertex (diagonalFiberTransport p f' t)) hvcurve) HEq.rfl
    (leftFibrationPrism_diagonal_heq_interval_of_base p f' g' (r ≫ β) h₀ h₁
      (r ≫ W') s₀' s₁' hp' c hc)
    (leftFibrationPrism_diagonal_heq_interval_of_base p f g (r ≫ β) h₀ h₁
      (r ≫ W) s₀ s₁ hp c hc) (changeCurve hvcurve) h

end SerrePositivity.InfinityCategories.F2
