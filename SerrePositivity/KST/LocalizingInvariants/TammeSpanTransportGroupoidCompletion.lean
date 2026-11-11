module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.TammeDenominatorGroupoidComparison
public import SerrePositivity.KST.LocalizingInvariants.FiberTransportGroupoidCompletion

/-!
概要：元の span 族の分母上の実輸送関手は、亜群化後に同値となる。
方針：全辺分母の区間上の両側 fibration 性と、与えた prism を保つ一般比較を適用する。
規約：輸送の選択を置き換えない。使われ方：fiber ごとの亜群化の分母に沿う降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma tammeSpanTransport_groupoidCompletion_isEquivalence
    (x : (laxCategory p q).obj _⦋0⦌) (b : (Δ[1] : SSet.{u}) ⟶ (laxCategory p q).obj)
    (hW : ∀ e : (Δ[1] : SSet.{u}) _⦋1⦌,
      b.app (Opposite.op ⦋1⦌) e ∈ tammeLocalizingEdges p q) :
    let π := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x
    ∀ (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
      (H : (Δ[1] : SSet.{u}) ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily (laxCategory p q).obj (tammeLocalizingEdges p q) x),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι π (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) →
      H ≫ π = fst (Δ[1] : SSet.{u}) _ ≫ b →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f) := by
  dsimp only
  have := tammeSpanDenominatorBaseChange_cartesianFibration p q x b hW
  have := tammeSpanBaseChange_cocartesianFibration p q x b
  exact fiberTransport_groupoidCompletion_isEquivalence _ b

lemma tammeDenominatorSpanTransport_groupoidCompletion_isEquivalence
    (x : (laxCategory p q).obj _⦋0⦌)
    (s : (laxCategory p q).obj _⦋1⦌) (hs : s ∈ tammeLocalizingEdges p q) :
    let π := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x
    ∀ (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber π ((laxCategory p q).obj.δ 1 s) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber π ((laxCategory p q).obj.δ 0 s))
      (H : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber π ((laxCategory p q).obj.δ 1 s) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily (laxCategory p q).obj (tammeLocalizingEdges p q) x),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι π ((laxCategory p q).obj.δ 1 s) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι π ((laxCategory p q).obj.δ 0 s) →
      H ≫ π = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm s →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f) := by
  have h₀ := intervalMap_source (SSet.yonedaEquiv.symm s)
  have h₁ := intervalMap_target (SSet.yonedaEquiv.symm s)
  rw [Equiv.apply_symm_apply] at h₀ h₁
  exact h₀.symm ▸ h₁.symm ▸ tammeSpanTransport_groupoidCompletion_isEquivalence p q x
    (SSet.yonedaEquiv.symm s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.tammeDenominatorInterval_edges_mem p q s hs)

end SerrePositivity.KST.LocalizingInvariants
