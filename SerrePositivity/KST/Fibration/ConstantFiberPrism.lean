module
public import SerrePositivity.KST.Fibration.SectionEdgePrism
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # 底で定値となる同じ実 prism の、指定 fiber 内のホモトピーへの持ち上げ -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の prism を、全パラメータと両端を固定したまま同じ fiber 内へ持ち上げる。 -/
def constantFiberPrismHomotopy {P E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f g : P ⟶ vertexFiber p b) (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (h₀ : prismEndpoint 0 P ≫ H = f ≫ vertexFiberι p b)
    (h₁ : prismEndpoint 1 P ≫ H = g ≫ vertexFiberι p b)
    (hp : H ≫ p = SSet.const b) : SSet.Homotopy f g where
  h := (β_ P (Δ[1] : SSet.{u})).hom ≫ vertexFiberLift p b H hp
  h₀ := by
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, Category.assoc, vertexFiberLift_ι]
    change prismEndpoint 0 P ≫ H = f ≫ vertexFiberι p b
    exact h₀
  h₁ := by
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, Category.assoc, vertexFiberLift_ι]
    change prismEndpoint 1 P ≫ H = g ≫ vertexFiberι p b
    exact h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 同じ fiber 内の端点は anodyne 局所化で等しい。底の全空間での等式だけにはしない。 -/
theorem constantFiberPrism_localized_eq {P E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f g : P ⟶ vertexFiber p b) (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (h₀ : prismEndpoint 0 P ≫ H = f ≫ vertexFiberι p b)
    (h₁ : prismEndpoint 1 P ≫ H = g ≫ vertexFiberι p b)
    (hp : H ≫ p = SSet.const b) :
    AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g :=
  AnodyneHomotopy.map_homotopy_eq _ SSet.anodyneExtensions.Q_inverts
    (constantFiberPrismHomotopy p b f g H h₀ h₁ hp)

end SerrePositivity.KST.Fibration
