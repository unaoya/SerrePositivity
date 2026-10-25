module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionIntervalSourceSquare
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportIntervalComparisonPresentation

/-!
概要：両端の表示変更を明示した、元の区間比較の始点正方形。
方針：両端を指定評価へ揃えてから、元の全延長正方形へ帰着する。
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

include ha hb in
/-- 元の指定区間比較の正方形を、同じ実端点の明示的表示で読む。 -/
lemma relativeExtensionInterval_source_square_at_endpoints
    (j₀ j₁ : A ⟶ D) (hj₀ : prismEndpoint 0 A ≫ r = j₀)
    (hj₁ : prismEndpoint 1 A ≫ r = j₁)
    (hj₀β : j₀ ≫ β = SSet.const a) (hj₁β : j₁ ≫ β = SSet.const b)
    (hj₀W : j₀ ≫ W = f ≫ vertexFiberι p a)
    (hj₀W' : j₀ ≫ W' = f' ≫ vertexFiberι p a)
    (hj₁W : j₁ ≫ W = g ≫ vertexFiberι p b)
    (hj₁W' : j₁ ≫ W' = g' ≫ vertexFiberι p b) :
    relativeExtensionFiberEndpoint_witnessIso p β i hi v hv j₁ b hj₁β
        W W' hW hW' hWi hWi' g g' hj₁W hj₁W' ≪≫
      leftFibrationPrism_transportIntervalIso p f' g' c (r ≫ W') s₀' s₁' ((hp').trans hc) =
      leftFibrationPrism_transportIntervalIso p f g c (r ≫ W) s₀ s₁ ((hp).trans hc) ≪≫
        diagonalFiberTransport_sourceIso p
          (relativeExtensionFiberEndpoint_witnessIso p β i hi v hv j₀ a hj₀β
            W W' hW hW' hWi hWi' f f' hj₀W hj₀W') c := by
  cases hj₀
  cases hj₁
  exact relativeExtensionInterval_source_square p β i hi v hv
    W W' hW hW' hWi hWi' r a b ha hb f f' g g' hs hs' he he' c hc

end SerrePositivity.InfinityCategories.F2
