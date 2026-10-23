module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismEvaluation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismComparisonWitness
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoComponentNaturality

/-!
概要：同じ全相対関手の実 prism から、全始点・全終点に自然な指定対角比較を得る。
方針：全係数の同じ実 prism を比較して curry し、元の指定同型の自然性を使う。
規約：全係数・元の指定比較を保持。使われ方：二辺比較の中間・終点の同時整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B) (a b : B _⦋0⦌)
  (h₀ : prismEndpoint 0 A ≫ β = SSet.const a)
  (h₁ : prismEndpoint 1 A ≫ β = SSet.const b)
local notation "R" => relativeFunctorSpace p β
local notation "P" => A ⊗ R
local notation "γ" => (Δ[1] ◁ fst A R) ≫ β
local notation "f" => relativePrismEvaluationEndpoint p β 0 a h₀
local notation "g" => relativePrismEvaluationEndpoint p β 1 b h₁
local notation "c" => intervalMappingCurryOfEndpoints γ
  (relativePrismEvaluation_base_endpoint p β 0 a h₀)
  (relativePrismEvaluation_base_endpoint p β 1 b h₁)

/-- 同じ全相対関手の元の実 prism と対角普遍 prism の指定比較。 -/
def relativePrismDiagonalComparison : FunctorIso g (diagonalFiberTransport p f c) :=
  leftFibrationPrism_diagonalTransportIso p f g γ
    (relativePrismEvaluation_base_endpoint p β 0 a h₀)
    (relativePrismEvaluation_base_endpoint p β 1 b h₁)
    (relativePrismEvaluationPrism p β)
    (relativePrismEvaluationEndpoint_ι p β 0 a h₀)
    (relativePrismEvaluationEndpoint_ι p β 1 b h₁)
    (relativePrismEvaluationPrism_projection p β)

/-- 同じ元の実 prism の全比較を、全相対関手の上の同じ指定同型として保持する。 -/
def relativePrismDiagonalComparisonCurry :
    FunctorIso (curry g) (curry (diagonalFiberTransport p f c)) :=
  (relativePrismDiagonalComparison p β a b h₀ h₁).curry

/-- 始点・終点が同時に動く元の全相対関手の比較は、同じ指定成分の正方形に自然。 -/
lemma relativePrismDiagonalComparison_naturality {s t : R _⦋0⦌} (e : VertexIso s t) :
    VertexIso.map e (curry g) ≪≫
      (relativePrismDiagonalComparisonCurry p β a b h₀ h₁).app t =
    (relativePrismDiagonalComparisonCurry p β a b h₀ h₁).app s ≪≫
      VertexIso.map e (curry (diagonalFiberTransport p f c)) := by
  exact functorIso_app_vertexIso_naturality
    (relativePrismDiagonalComparisonCurry p β a b h₀ h₁) e

end SerrePositivity.InfinityCategories.F2
