module
public import SerrePositivity.KST.Fibration.WeakSpanDenominatorBaseChange
public import SerrePositivity.KST.LocalizingInvariants.FiberTransportGroupoidCompletion

/-! # 元の W 分母上の指定した実輸送関手の亜群化による同値性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q)

include h in
lemma weakSpanTransport_groupoidCompletion_isEquivalence
    (x : B.obj _⦋0⦌) (b : (Δ[1] : SSet.{u}) ⟶ B.obj)
    (hW : ∀ e : (Δ[1] : SSet.{u}) _⦋1⦌,
      b.app (Opposite.op ⦋1⦌) e ∈ weakEquivalences i) :
    let π := markedSpanFamilyProjection B.obj (weakEquivalences i) x
    ∀ (f : vertexFiber π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ⟶
      vertexFiber π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
      (H : (Δ[1] : SSet.{u}) ⊗
        vertexFiber π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ⟶
        markedSpanFamily B.obj (weakEquivalences i) x),
      prismEndpoint 0 _ ≫ H =
        vertexFiberι π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) →
      prismEndpoint 1 _ ≫ H = f ≫
        vertexFiberι π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) →
      H ≫ π = fst (Δ[1] : SSet.{u}) _ ≫ b →
      IsSimplicialHomotopyEquivalence (groupoidCompletionMapOf f) := by
  dsimp only
  have := weakSpanDenominatorBaseChange_cartesianFibration h x b hW
  have := weakSpanBaseChange_cocartesianFibration (i := i) x b
  exact fiberTransport_groupoidCompletion_isEquivalence _ b

end SerrePositivity.KST.Fibration
