module
public import SerrePositivity.InfinityCategories.Core.FunctorRelativeTerminal
public import SerrePositivity.InfinityCategories.Core.ConeTerminalBoundary
public import SerrePositivity.InfinityCategories.Core.FiberwiseHomotopy
/-!
概要：相対終対象の切断による全パラメータの底を固定した比較。
方針：元の相対境界充填と right fibration の表現を実射へ接続する。
規約：安定性や有限余極限を仮定しない。使われ方：HA 1.4.2.27 の余錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma relativeTerminalFamilyComparison_exists {K E B : SSet.{u}} (p : E ⟶ B)
    (f g : K ⟶ E) (hfg : f ≫ p = g ≫ p)
    (ht : ∀ k : K _⦋0⦌, TerminalBoundaryLifting p (g.app (Opposite.op ⦋0⦌) k)) :
    ∃ e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj E))
        (functorVertex f) (functorVertex g),
      (e.map ((truncation 2).map ((ihom K).map p))).edge =
        PinchedHom.constant (functorVertex (f ≫ p)) 1 := by
  let q := (ihom K).map p
  let fp := functorVertex (f ≫ p)
  let x : (vertexFiber q fp) _⦋0⦌ := ⟨functorVertex f, by
    rw [pinchedConstant_zero]
    rfl⟩
  let y : (vertexFiber q fp) _⦋0⦌ := ⟨functorVertex g, by
    rw [pinchedConstant_zero]
    change functorVertex (g ≫ p) = functorVertex (f ≫ p)
    rw [hfg]⟩
  have hy : IsTerminalVertex y := TerminalBoundaryLifting.isTerminalVertex_fiber q fp y
    (terminalBoundaryLifting_ihom_of_pointwise p g ht)
  obtain ⟨e⟩ := hy.nonempty_edge x
  exact ⟨e.map ((truncation 2).map (vertexFiberι q fp)), e.edge.property⟩
lemma relativeTerminalFamilyHomotopy_exists {K E B : SSet.{u}} (p : E ⟶ B)
    (f g : K ⟶ E) (hfg : f ≫ p = g ≫ p)
    (ht : ∀ k : K _⦋0⦌, TerminalBoundaryLifting p (g.app (Opposite.op ⦋0⦌) k)) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = CartesianMonoidalCategory.fst K (Δ[1] : SSet.{u}) ≫ f ≫ p := by
  obtain ⟨e, he⟩ := relativeTerminalFamilyComparison_exists p f g hfg ht
  exact ⟨simplicialHomotopyOfFunctorEdge e,
    simplicialHomotopyOfFunctorEdge_comp_eq_constant p (f ≫ p) e he⟩
lemma relativeTerminalSectionComparison_exists {E B : SSet.{u}} (p : E ⟶ B)
    (r : B ⟶ E) (hr : r ≫ p = 𝟙 B)
    (ht : ∀ b : B _⦋0⦌, TerminalBoundaryLifting p (r.app (Opposite.op ⦋0⦌) b)) :
    ∃ e : Truncated.Edge (X := (truncation 2).obj ((ihom E).obj E))
        (functorVertex (𝟙 E)) (functorVertex (p ≫ r)),
      (e.map ((truncation 2).map ((ihom E).map p))).edge =
        PinchedHom.constant (functorVertex p) 1 := by
  simpa only [Category.id_comp] using
    relativeTerminalFamilyComparison_exists p (𝟙 E) (p ≫ r)
      (by rw [Category.id_comp, Category.assoc, hr, Category.comp_id])
      (fun a ↦ ht (p.app _ a))
lemma relativeTerminalSectionHomotopy_exists {E B : SSet.{u}} (p : E ⟶ B)
    (r : B ⟶ E) (hr : r ≫ p = 𝟙 B)
    (ht : ∀ b : B _⦋0⦌, TerminalBoundaryLifting p (r.app (Opposite.op ⦋0⦌) b)) :
    ∃ H : SSet.Homotopy (𝟙 E) (p ≫ r),
      H.h ≫ p = CartesianMonoidalCategory.fst E (Δ[1] : SSet.{u}) ≫ p := by
  obtain ⟨e, he⟩ := relativeTerminalSectionComparison_exists p r hr ht
  exact ⟨simplicialHomotopyOfFunctorEdge e,
    simplicialHomotopyOfFunctorEdge_comp_eq_constant p p e he⟩
end SerrePositivity.InfinityCategories
