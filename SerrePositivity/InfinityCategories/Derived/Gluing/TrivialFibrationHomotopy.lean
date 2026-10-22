module
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-! 自明 Kan fibration への合成が等しい二写像を、全パラメータを保つ実ホモトピーで結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial

def dgGluingHomotopy_of_trivialFibration_post_eq {A E B : SSet.{u}}
    [Quasicategory E] (p : E ⟶ B)
    [TrivialKanFibration p] (f g : A ⟶ E) (h : f ≫ p = g ≫ p) : SSet.Homotopy f g := by
  let q := (ihom A).map p
  let b := functorVertex (g ≫ p)
  have hc := vertexFiber_isContractibleKan q b
  have := hc.kanComplex
  let v₀ : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex f, by
    rw [pinchedConstant_zero]
    change functorVertex (f ≫ p) = functorVertex (g ≫ p)
    rw [h]⟩
  let v₁ : (vertexFiber q b) _⦋0⦌ := ⟨functorVertex g, by
    rw [pinchedConstant_zero]
    rfl⟩
  let e := VertexIso.map (terminalVertexIso (hc.isTerminalVertex v₀)
    (hc.isTerminalVertex v₁)) (vertexFiberι q b)
  exact simplicialHomotopyOfFunctorEdge (FunctorIso.edge e)

end SerrePositivity.InfinityCategories
