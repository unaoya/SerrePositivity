module

public import SerrePositivity.InfinityCategories.F2.RelativePrismEvaluation
public import SerrePositivity.InfinityCategories.F2.RelativeUncurryPointVertices

/-!
概要：全相対関手上の実 prism と実端点を、元の実相対関手で評価して厳密に回収する。
方針：元の相対 uncurry の一点頂点の式と、同じ実係数射を使う。
規約：元の実 prism・全始点・全終点を保持。使われ方：二辺比較の指定値への復帰。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B A : SSet.{u}} (p : E ⟶ B) (β : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
  (W : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (hW : W ≫ p = β)
local notation "v" => relativeFunctorVertex p β W hW
local notation "r" => lift (𝟙 A) (SSet.const v)

/-- 元の実相対関手で全評価 prism を評価すると、その同じ実 prism 自体を回収する。 -/
lemma relativePrismEvaluationPrism_at_vertex :
    (Δ[1] ◁ r) ≫ relativePrismEvaluationPrism p β = W := by
  rw [relativePrismEvaluationPrism, ← Category.assoc]
  have h : (Δ[1] ◁ r) ≫ (α_ (Δ[1] : SSet.{u}) A _).inv =
      lift (𝟙 ((Δ[1] : SSet.{u}) ⊗ A)) (SSet.const v) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [h]
  apply functorVertex_injective
  exact congrArg Subtype.val (relativeFunctorUncurry_point_vertex p β (𝟙 _) v)

/-- 元の実相対関手の実 fiber 端点も、全相対関手上の同じ実端点評価で厳密に回収する。 -/
lemma relativePrismEvaluationEndpoint_at_vertex (i : Fin 2) (z : B _⦋0⦌)
    (h : prismEndpoint i A ≫ β = SSet.const z) (g : A ⟶ vertexFiber p z)
    (hg : prismEndpoint i A ≫ W = g ≫ vertexFiberι p z) :
    r ≫ relativePrismEvaluationEndpoint p β i z h = g := by
  apply vertexFiber_hom_ext p z
  rw [Category.assoc, ← relativePrismEvaluationEndpoint_ι, ← Category.assoc,
    ← prismEndpoint_naturality, Category.assoc, relativePrismEvaluationPrism_at_vertex]
  exact hg

end SerrePositivity.InfinityCategories.F2
