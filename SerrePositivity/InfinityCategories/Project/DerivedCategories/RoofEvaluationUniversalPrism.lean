module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofEvaluationLiftSpace
/-!
概要：全評価選択空間上の普遍実 prism を、始端と全底の厳密な等式付きで構成する。
方針：普遍関手族を uncurry し、区間を第一因子に保つ結合子で展開する。
規約：選択点ごとに prism を取り直さない。使われ方：全高次の評価比較の相対整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K E B : SSet.{u}} (p : E ⟶ B) (a : K ⟶ E)
variable (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B) (hγ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ γ)
/-- 指定始端と底を持つ、全実評価選択空間上の普遍 prism。 -/
def roofEvaluationUniversalPrism :
    (Δ[1] : SSet.{u}) ⊗ (K ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ) ⟶ E :=
  (α_ (Δ[1] : SSet.{u}) K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ)).inv ≫
    uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftCurry p a γ hγ)
/-- 普遍 prism の全底は、選択パラメータを忘れた同じ指定底 prism。 -/
lemma roofEvaluationUniversalPrism_over :
    roofEvaluationUniversalPrism p a γ hγ ≫ p =
      (Δ[1] ◁ fst K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ)) ≫ γ := by
  rw [roofEvaluationUniversalPrism, Category.assoc, ← uncurry_natural_right,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftCurry_over, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  rfl
/-- 普遍 prism の始端は、同じ全選択空間上で元の実初期図式に厳密に一致。 -/
lemma roofEvaluationUniversalPrism_start :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ) ≫
      roofEvaluationUniversalPrism p a γ hγ = fst K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ) ≫ a := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ) ≫
      (α_ (Δ[1] : SSet.{u}) K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ)).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ▷ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ := rfl
  rw [roofEvaluationUniversalPrism, ← Category.assoc, he, ← uncurry_pre_app,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftCurry_start, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
