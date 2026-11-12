module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismDiagonalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEvaluationVertex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPointComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismComparisonPrecomp
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismBoundaryEquality

/-!
概要：全相対関手上の指定対角比較の実一点成分は、元の同じ実 prism の指定比較。
方針：curry の一点評価と実 prism の制限を保ち、同じ元の実データへ戻す。
規約：比較を再選択しない。使われ方：始点も動く二辺比較の同じ指定値の自然性。
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
local notation "F" => relativePrismEvaluationEndpoint p β 0 a h₀
local notation "G" => relativePrismEvaluationEndpoint p β 1 b h₁
local notation "hF" => relativePrismEvaluation_base_endpoint p β 0 a h₀
local notation "hG" => relativePrismEvaluation_base_endpoint p β 1 b h₁
local notation "U" => relativePrismEvaluationPrism p β

/-- 同じ全比較の一点成分は、元の実始点・実終点・実 prism による指定対角比較。 -/
lemma relativePrismDiagonalComparison_at_vertex
    (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β)
    (f : A ⟶ vertexFiber p a) (g : A ⟶ vertexFiber p b)
    (hs : prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 A ≫ W = g ≫ vertexFiberι p b) :
    HEq ((relativePrismDiagonalComparisonCurry p β a b h₀ h₁).app
      (relativeFunctorVertex p β W hW))
      (leftFibrationPrism_diagonalTransportIso p f g β h₀ h₁ W hs he hW) := by
  let v := relativeFunctorVertex p β W hW
  let r := lift (𝟙 A) (SSet.const v)
  have hc := functorIso_curry_app_heq_precomp
    (relativePrismDiagonalComparison p β a b h₀ h₁) v
  have hs' := relativePrismEvaluationEndpoint_ι p β 0 a h₀
  have he' := relativePrismEvaluationEndpoint_ι p β 1 b h₁
  have h₀' : prismEndpoint 0 A ≫ ((Δ[1] ◁ r) ≫ γ) = SSet.const a := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hF, SSet.comp_const]
  have h₁' : prismEndpoint 1 A ≫ ((Δ[1] ◁ r) ≫ γ) = SSet.const b := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hG, SSet.comp_const]
  have hp := leftFibrationPrism_diagonalTransportIso_precomp_heq p F G γ hF hG U
    hs' he' (relativePrismEvaluationPrism_projection p β) r h₀' h₁'
  refine hc.trans (hp.trans ?_)
  apply diagonalTransportIso_heq_of_boundary
  · rfl
  · rfl
  · exact relativePrismEvaluationPrism_at_vertex p β W hW

end SerrePositivity.InfinityCategories.F2
