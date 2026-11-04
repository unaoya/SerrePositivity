module
public import SerrePositivity.KST.Fibration.WeakSpanTransportGroupoidCompletion
public import SerrePositivity.KST.LocalizingInvariants.IntervalMarkedEdges

/-! # 元の各 W 辺に沿う指定した分数 span 輸送の亜群化同値 -/

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
include h

/-- 元の全一単体上で、W は同じ商関手が反転する辺のクラスに一致する。 -/
theorem weakEquivalences_eq_invertedEdges : weakEquivalences i = invertedEdges q.hom := by
  ext s
  exact mem_weakEquivalences_iff_invertible h (edgeOfSimplex s)

/-- 指定した W 辺の区間図式は、両端の恒等も含む全辺を W に送る。 -/
theorem weakDenominatorInterval_edges_mem (s : B.obj _⦋1⦌) (hs : s ∈ weakEquivalences i)
    (e : (Δ[1] : SSet.{u}) _⦋1⦌) :
    (SSet.yonedaEquiv.symm s).app (Opposite.op ⦋1⦌) e ∈ weakEquivalences i := by
  apply intervalMap_edges_mem _ _ s hs e
  intro x
  rw [weakEquivalences_eq_invertedEdges h]
  exact invertedEdges_constant q.hom x

lemma weakDenominatorSpanTransport_groupoidCompletion_isEquivalence
    (x : B.obj _⦋0⦌)
    (s : B.obj _⦋1⦌) (hs : s ∈ weakEquivalences i) :
    let π := markedSpanFamilyProjection B.obj (weakEquivalences i) x
    ∀ (f : vertexFiber π (B.obj.δ 1 s) ⟶
        vertexFiber π (B.obj.δ 0 s))
      (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber π (B.obj.δ 1 s) ⟶
        markedSpanFamily B.obj (weakEquivalences i) x),
      prismEndpoint 0 _ ≫ H = vertexFiberι π (B.obj.δ 1 s) →
      prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι π (B.obj.δ 0 s) →
      H ≫ π = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm s →
      IsSimplicialHomotopyEquivalence (groupoidCompletionMapOf f) := by
  have h₀ := intervalMap_source (SSet.yonedaEquiv.symm s)
  have h₁ := intervalMap_target (SSet.yonedaEquiv.symm s)
  rw [Equiv.apply_symm_apply] at h₀ h₁
  exact h₀.symm ▸ h₁.symm ▸ weakSpanTransport_groupoidCompletion_isEquivalence h x
    (SSet.yonedaEquiv.symm s) (weakDenominatorInterval_edges_mem h s hs)


end SerrePositivity.KST.Fibration
