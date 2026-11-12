module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofEvaluationUniversalPrism
/-!
概要：終端の底が指定頂点に定値な普遍評価 prism を、同じ全選択空間上で実 fiber に戻す。
方針：普遍 prism の終端を fiber に持ち上げ、元の全円柱を実ホモトピーとして保持する。
規約：評価空間の各点で選び直さない。使われ方：全境界を充填する実評価の普遍族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
/-- 全評価選択空間上の fiber への普遍評価と、同じ全円柱・底を持つ実ホモトピー。 -/
structure RoofUniversalFiberEvaluation {K E B : SSet.{u}} (p : E ⟶ B) (t : B _⦋0⦌)
    (a : K ⟶ E) (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (hγ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ γ) where
  value : K ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p t
  homotopy : SSet.Homotopy (fst K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ) ≫ a)
    (value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t)
  raw : homotopy.h =
    (β_ (K ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ) (Δ[1] : SSet.{u})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationUniversalPrism p a γ hγ
  projection : homotopy.h ≫ p =
    (β_ (K ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ) (Δ[1] : SSet.{u})).hom ≫
      (Δ[1] ◁ fst K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ)) ≫ γ
/-- 終端の底が定値なら、全選択空間上の同じ prism から普遍的な実 fiber 評価を回収できる。 -/
def roofEvaluationUniversalFiber {K E B : SSet.{u}} (p : E ⟶ B) (t : B _⦋0⦌)
    (a : K ⟶ E) (γ : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (hγ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ γ)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ γ = SSet.const t) :
    RoofUniversalFiberEvaluation p t a γ hγ := by
  let S := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationLiftSpace p a γ hγ
  let U := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationUniversalPrism p a γ hγ
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ S) ≫ U
  have hv : v ≫ p = SSet.const t := by
    dsimp only [v, U]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationUniversalPrism_over, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h₁, SSet.comp_const]
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p t v hv
  let H : SSet.Homotopy (fst K S ≫ a) (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p t) := {
    h := (β_ (K ⊗ S) (Δ[1] : SSet.{u})).hom ≫ U
    h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationUniversalPrism_start p a γ hγ
    h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p t v hv).symm
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  refine ⟨f, H, rfl, ?_⟩
  change ((β_ (K ⊗ S) (Δ[1] : SSet.{u})).hom ≫ U) ≫ p = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluationUniversalPrism_over]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
