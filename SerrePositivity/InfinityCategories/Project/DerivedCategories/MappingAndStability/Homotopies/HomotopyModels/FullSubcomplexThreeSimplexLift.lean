module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.FullSubcomplexEdgeLift

/-! # 二つの指定面から実三単体を全部分複体へ持ち上げる

概要：実三単体の零面と一面が全部分複体にあれば、全三単体を同じ台で持ち上げる。
方針：四頂点は零面と一面で覆われる。使われ方：高次の実 over 充填の分母部分圏への回収。
規約：入力の台と全指定面を厳密に保存する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

/-- 指定零面・一面の所属から、同じ実三単体を全部分複体へ持ち上げる。 -/
def fullSubcomplexThreeSimplexLift (T : X _⦋3⦌)
    (F₀ F₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋2⦌)
    (h₀ : X.δ 0 T = F₀.val) (h₁ : X.δ 1 T = F₁.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋3⦌ := by
  refine ⟨T, ?_⟩
  intro v
  generalize hi : v.toOrderHom 0 = i
  fin_cases i
  · have he : v = (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3)) ≫
        SimplexCategory.δ (1 : Fin 4) := SimplexCategory.Hom.ext_zero_left _ _ hi
    rw [he, op_comp, Functor.map_comp_apply]
    change P (X.map _ (X.δ 1 T))
    rw [h₁]
    exact F₁.property _
  · have he : v = (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3)) ≫
        SimplexCategory.δ (0 : Fin 4) := SimplexCategory.Hom.ext_zero_left _ _ hi
    rw [he, op_comp, Functor.map_comp_apply]
    change P (X.map _ (X.δ 0 T))
    rw [h₀]
    exact F₀.property _
  · have he : v = (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3)) ≫
        SimplexCategory.δ (0 : Fin 4) := SimplexCategory.Hom.ext_zero_left _ _ hi
    rw [he, op_comp, Functor.map_comp_apply]
    change P (X.map _ (X.δ 0 T))
    rw [h₀]
    exact F₀.property _
  · have he : v = (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3)) ≫
        SimplexCategory.δ (0 : Fin 4) := SimplexCategory.Hom.ext_zero_left _ _ hi
    rw [he, op_comp, Functor.map_comp_apply]
    change P (X.map _ (X.δ 0 T))
    rw [h₀]
    exact F₀.property _

/-- 持ち上げた実三単体の台は、元の三単体そのもの。 -/
lemma fullSubcomplexThreeSimplexLift_val (T : X _⦋3⦌)
    (F₀ F₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋2⦌)
    (h₀ : X.δ 0 T = F₀.val) (h₁ : X.δ 1 T = F₁.val) :
    (fullSubcomplexThreeSimplexLift P T F₀ F₁ h₀ h₁).val = T := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
