module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismDiagonalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEvaluationVertex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCurryPointVertex
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonPrecomp

/-!
概要：全相対関手の curry した実端点と普遍対角終点を、同じ元の実射の頂点へ戻す。
方針：curry の一点評価、元の実 prism の評価、同じ対角輸送の係数制限を使う。
規約：端点の等式を実射から証明する。使われ方：始点も動く指定比較の正方形の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実相対関手の同じ実端点は、curry した全端点評価の同じ頂点。 -/
lemma relativePrismEvaluationEndpoint_curry_vertex {E B A : SSet.{u}}
    (p : E ⟶ B) (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β)
    (i : Fin 2) (z : B _⦋0⦌) (h : prismEndpoint i A ≫ β = SSet.const z)
    (g : A ⟶ vertexFiber p z) (hg : prismEndpoint i A ≫ W = g ≫ vertexFiberι p z) :
    (curry (relativePrismEvaluationEndpoint p β i z h)).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex p β W hW) = functorVertex g := by
  rw [functorCurry_point_vertex, relativePrismEvaluationEndpoint_at_vertex p β W hW i z h g hg]

variable {E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B) (a b : B _⦋0⦌)
  (h₀ : prismEndpoint 0 A ≫ β = SSet.const a)
  (h₁ : prismEndpoint 1 A ≫ β = SSet.const b)
local notation "R" => relativeFunctorSpace p β
local notation "γ" => (Δ[1] ◁ fst A R) ≫ β
local notation "F" => relativePrismEvaluationEndpoint p β 0 a h₀
local notation "hF" => relativePrismEvaluation_base_endpoint p β 0 a h₀
local notation "hG" => relativePrismEvaluation_base_endpoint p β 1 b h₁
local notation "c" => intervalMappingCurryOfEndpoints γ hF hG

/-- 同じ元の実相対関手の普遍対角終点も、同じ元の全初期値からの対角輸送の頂点。 -/
lemma relativePrismDiagonalNative_curry_vertex
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β)
    (f : A ⟶ vertexFiber p a) (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a) :
    (curry (diagonalFiberTransport p F c)).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex p β W hW) =
      functorVertex (diagonalFiberTransport p f (intervalMappingCurryOfEndpoints β h₀ h₁)) := by
  let r := lift (𝟙 A) (SSet.const (relativeFunctorVertex p β W hW))
  have hc : r ≫ c = intervalMappingCurryOfEndpoints β h₀ h₁ := by
    apply intervalMappingUncurry_injective
    rw [intervalMappingUncurry_precomp, intervalMappingUncurry_curryOfEndpoints,
      intervalMappingUncurry_curryOfEndpoints]
    change (Δ[1] ◁ r) ≫ ((Δ[1] ◁ fst A R) ≫ β) = β
    rw [← whiskerLeft_comp_assoc, lift_fst, whiskerLeft_id, Category.id_comp]
  rw [functorCurry_point_vertex, diagonalFiberTransport_precomp]
  change functorVertex (diagonalFiberTransport p (r ≫ F) (r ≫ c)) = _
  rw [hc, relativePrismEvaluationEndpoint_at_vertex p β W hW 0 a h₀ f hs]

end SerrePositivity.InfinityCategories.F2
