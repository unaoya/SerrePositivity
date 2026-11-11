module
public import SerrePositivity.KST.Fibration.ConstantFiberPrism

/-! # 元の全パラメータ prism の端点の anodyne 局所化での等式 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の prism の両端を変えず、同じ全パラメータの単体的ホモトピーに読む。 -/
def prismHomotopy {P E : SSet.{u}} (f g : P ⟶ E) (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P ≫ H = f) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P ≫ H = g) :
    SSet.Homotopy f g where
  h := (β_ P (Δ[1] : SSet.{u})).hom ≫ H
  h₀ := h₀
  h₁ := h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 全空間へ値を取る元の prism の端点は局所化で等しい。 -/
theorem prism_localized_eq {P E : SSet.{u}} (f g : P ⟶ E)
    (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P ≫ H = f) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P ≫ H = g) :
    AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g :=
  AnodyneHomotopy.map_homotopy_eq _ SSet.anodyneExtensions.Q_inverts
    (prismHomotopy f g H h₀ h₁)

end SerrePositivity.KST.Fibration
