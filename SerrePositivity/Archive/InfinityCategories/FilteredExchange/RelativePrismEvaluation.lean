module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：同じ底の区間上の全相対関手を、全係数上の一つの実 prism として評価する。
方針：相対関手空間の恒等族を展開し、結合子で区間を左端へ移す。
規約：全相対関手・底・端点を保持。使われ方：始点も動く二辺比較の全族自然性。
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
local notation "R" => relativeFunctorSpace p β
local notation "P" => A ⊗ R
local notation "b" => (Δ[1] ◁ fst A R) ≫ β

/-- 同じ底上の全相対関手を全係数で同時に評価する元の実 prism。 -/
def relativePrismEvaluationPrism : (Δ[1] : SSet.{u}) ⊗ P ⟶ E :=
  (α_ (Δ[1] : SSet.{u}) A R).inv ≫ relativeFunctorUncurry (𝟙 R)

/-- 全相対関手の同時評価は、元の同じ底の区間を第一係数で被覆する。 -/
lemma relativePrismEvaluationPrism_projection :
    relativePrismEvaluationPrism p β ≫ p = b := by
  rw [relativePrismEvaluationPrism, Category.assoc, relativeFunctorUncurry_projection]
  have h : (α_ (Δ[1] : SSet.{u}) A R).inv ≫ fst (Δ[1] ⊗ A) R =
      Δ[1] ◁ fst A R := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, h]

/-- 元の底の端点表示は、全相対関手を動かしても同じ端点表示。 -/
lemma relativePrismEvaluation_base_endpoint (i : Fin 2) (z : B _⦋0⦌)
    (h : prismEndpoint i A ≫ β = SSet.const z) :
    prismEndpoint i P ≫ b = SSet.const z := by
  rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h, SSet.comp_const]

/-- 元の全相対関手の同時評価の同じ実端点を、指定された実 fiber に読む。 -/
def relativePrismEvaluationEndpoint (i : Fin 2) (z : B _⦋0⦌)
    (h : prismEndpoint i A ≫ β = SSet.const z) : P ⟶ vertexFiber p z :=
  vertexFiberLift p z (prismEndpoint i P ≫ relativePrismEvaluationPrism p β) (by
    rw [Category.assoc, relativePrismEvaluationPrism_projection,
      relativePrismEvaluation_base_endpoint p β i z h])

/-- 元の全相対関手の同じ実端点への包含は、同時評価の実 prism の端点そのもの。 -/
lemma relativePrismEvaluationEndpoint_ι (i : Fin 2) (z : B _⦋0⦌)
    (h : prismEndpoint i A ≫ β = SSet.const z) :
    prismEndpoint i P ≫ relativePrismEvaluationPrism p β =
      relativePrismEvaluationEndpoint p β i z h ≫ vertexFiberι p z :=
  (vertexFiberLift_ι _ _ _ _).symm

end SerrePositivity.InfinityCategories.F2
