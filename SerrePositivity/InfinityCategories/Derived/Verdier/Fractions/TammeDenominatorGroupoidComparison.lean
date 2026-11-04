module

public import SerrePositivity.KST.LocalizingInvariants.TammeSpanDiagramFibers
public import SerrePositivity.KST.LocalizingInvariants.IntervalMarkedEdges
public import SerrePositivity.KST.LocalizingInvariants.IntervalFiberGroupoidCompletion
public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletionIso

/-!
概要：元の Tamme 分母の両端で、固定端点分数 span の亜群化を実同値で比較する。
方針：分母上の区間図式を両側 fibration にし、両端 fiber の同型を介して比較を戻す。
規約：反転済みの形式的な辺だけを入力にしない。使われ方：分数の fiber ごとの亜群化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma tammeDenominatorInterval_edges_mem (s : (laxCategory p q).obj _⦋1⦌)
    (hs : s ∈ tammeLocalizingEdges p q) (e : (Δ[1] : SSet.{u}) _⦋1⦌) :
    (SSet.yonedaEquiv.symm s).app (Opposite.op ⦋1⦌) e ∈ tammeLocalizingEdges p q := by
  apply intervalMap_edges_mem _ _ s hs e
  intro x
  rw [tammeLocalizingEdges_eq]
  exact invertedEdges_constant (laxDifference p q) x

def tammeSpanIntervalGroupoidEquivalence (x : (laxCategory p q).obj _⦋0⦌)
    (b : (Δ[1] : SSet.{u}) ⟶ (laxCategory p q).obj)
    (hW : ∀ e : (Δ[1] : SSet.{u}) _⦋1⦌,
      b.app (Opposite.op ⦋1⦌) e ∈ tammeLocalizingEdges p q) :
    QCatEquivalence
      (groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
      (groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) := by
  let π := pullback.snd
    (markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) b
  have : CartesianFibration π := tammeSpanDenominatorBaseChange_cartesianFibration p q x b hW
  have : CocartesianFibration π := tammeSpanBaseChange_cocartesianFibration p q x b
  exact (groupoidCompletionEquivalenceOfIso
      (tammeSpanDiagramFiberIso p q x b (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).trans
    ((intervalFiberGroupoidCompletionEquivalence π).trans
      (groupoidCompletionEquivalenceOfIso
        (tammeSpanDiagramFiberIso p q x b (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).symm)

def tammeDenominatorFixedSpanGroupoidEquivalence (x : (laxCategory p q).obj _⦋0⦌)
    (s : (laxCategory p q).obj _⦋1⦌) (hs : s ∈ tammeLocalizingEdges p q) :
    QCatEquivalence
      (groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        ((laxCategory p q).obj.δ 1 s)))
      (groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        ((laxCategory p q).obj.δ 0 s))) := by
  have h₀ := intervalMap_source (SSet.yonedaEquiv.symm s)
  have h₁ := intervalMap_target (SSet.yonedaEquiv.symm s)
  rw [Equiv.apply_symm_apply] at h₀ h₁
  exact h₀.symm ▸ h₁.symm ▸ tammeSpanIntervalGroupoidEquivalence p q x
    (SSet.yonedaEquiv.symm s) (tammeDenominatorInterval_edges_mem p q s hs)

end SerrePositivity.KST.LocalizingInvariants
