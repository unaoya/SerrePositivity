module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.TammeSpanDiagramFibers
public import SerrePositivity.KST.LocalizingInvariants.IntervalMarkedEdges
public import SerrePositivity.KST.LocalizingInvariants.IntervalFiberGroupoidCompletion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionIso

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

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
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) := by
  let π := pullback.snd
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) b
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration π := tammeSpanDenominatorBaseChange_cartesianFibration p q x b hW
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration π := tammeSpanBaseChange_cocartesianFibration p q x b
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfIso
      (tammeSpanDiagramFiberIso p q x b (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).trans
    ((intervalFiberGroupoidCompletionEquivalence π).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfIso
        (tammeSpanDiagramFiberIso p q x b (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).symm)

def tammeDenominatorFixedSpanGroupoidEquivalence (x : (laxCategory p q).obj _⦋0⦌)
    (s : (laxCategory p q).obj _⦋1⦌) (hs : s ∈ tammeLocalizingEdges p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        ((laxCategory p q).obj.δ 1 s)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        ((laxCategory p q).obj.δ 0 s))) := by
  have h₀ := intervalMap_source (SSet.yonedaEquiv.symm s)
  have h₁ := intervalMap_target (SSet.yonedaEquiv.symm s)
  rw [Equiv.apply_symm_apply] at h₀ h₁
  exact h₀.symm ▸ h₁.symm ▸ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence p q x
    (SSet.yonedaEquiv.symm s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorInterval_edges_mem p q s hs)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorInterval_edges_mem := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorInterval_edges_mem

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeDenominatorFixedSpanGroupoidEquivalence._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorFixedSpanGroupoidEquivalence._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.tammeSpanIntervalGroupoidEquivalence._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeSpanIntervalGroupoidEquivalence._proof_8
