module

public import SerrePositivity.InfinityCategories.F2.Ind.InitialEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafSubcategory
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaPresheafEvaluation
public import SerrePositivity.InfinityCategories.Core.UniverseZeroObjects

/-!
概要：元の小さい圏の始対象は、Indκ への同じ Yoneda 因子化でも始対象。
方針：Ind の評価値の終対象性を Yoneda の全写像空間比較と全部分包含で反映する。
規約：ℵ₀ ≤ κ を明示。使われ方：安定性に先立つ零対象の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 可縮 Kan 複体の元の頂点の終対象性を使い、同じ複体の宇宙持ち上げも可縮とする。 -/
lemma isContractibleKan_ulift {K : SSet.{u}} (hK : IsContractibleKan K) :
    IsContractibleKan ((SSet.uliftFunctor.{v, u}).obj K) := by
  apply isContractibleKan_of_nonempty_of_all_terminal
  · exact hK.nonempty.map ULift.up
  · rintro ⟨x⟩
    exact (isTerminalVertex_iff_ulift x).mp (hK.isTerminalVertex x)

/-- 同じ Ind Yoneda 頂点を前層へ含めると、元の表現可能前層の頂点そのもの。 -/
lemma indYoneda_vertex_inclusion (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) :
    (indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌)
      ((indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up z)) =
        functorVertex (representablePresheafInfinity z) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up z))
    (indYoneda_inclusion κ C)
  exact h.trans (yonedaInfinityMap_vertex z)

/-- 同じ元の Yoneda 因子化は、始対象を Indκ の始対象へ送る。 -/
lemma indYoneda_isInitial_of_initial (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {C : SSet.{u}} [Quasicategory C] {z : C _⦋0⦌} (hz : IsInitialVertex z) :
    IsInitialVertex ((indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up z)) := by
  apply F1B.kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro w
  let F := (presheafInfinityObjectEquiv C).symm w.val
  have hw : functorVertex F = w.val := (presheafInfinityObjectEquiv C).apply_symm_apply w.val
  have ht := indVertex_evaluation_isTerminal_of_initial κ hκ hz
    (fullSubcomplexOnVertices_vertex w)
  have ht' : IsTerminalVertex (F.app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm z))) := by
    rw [← hw] at ht
    have he := evaluateFunctorAt_functorVertex (ULift.up (SSet.opObjEquiv.symm z)) F
    exact (congrArg (fun s => IsTerminalVertex s) he).mp ht
  have hU := isContractibleKan_ulift.{u, u + 1}
    ((HomotopyLimits.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mp ht')
  have hm := (yonedaPresheafEvaluationEquivalence z F).isContractibleKan_iff.mpr hU
  apply ((indInclusionPresheaf_isFullyFaithful κ C) _ w).isContractibleKan_iff.mpr
  rw [indYoneda_vertex_inclusion]
  change IsContractibleKan (pinchedHom (functorVertex (representablePresheafInfinity z)) w.val)
  rw [← hw]
  exact hm

end SerrePositivity.InfinityCategories.F2.Ind
