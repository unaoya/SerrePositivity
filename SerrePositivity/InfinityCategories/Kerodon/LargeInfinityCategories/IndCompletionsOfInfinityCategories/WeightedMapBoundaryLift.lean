module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedSimplexRecovery
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：成分ごとの自明 Kan 比較から、weighted 比較の正次元の境界充填を構成する。
方針：元の最後の係数で相対境界を充填し、同じ境界と係数による一意性で像を固定。
規約：係数の Kan 性は不要。使われ方：元の twisted-arrow 全空間の前合成同値。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 成分ごとに自明 Kan な元の比較は、正次元で元の指定像を保つ境界充填を持つ。 -/
lemma exists_weightedMap_boundary_lift {I : Type u} [Category.{u} I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app i)]
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G (n + 1))
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (hsq : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm s) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      (boundary (n + 1)).ι ≫ H = a ∧ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η = SSet.yonedaEquiv.symm s := by
  have hG : (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G =
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm s.1 := by
    rw [hsq, Category.assoc, SSet.yonedaEquiv_symm_comp]
    rfl
  have hF : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm s.1 := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection η, ← Category.assoc]
    exact hG
  have hr : ((boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm s) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G = (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm s.1 :=
    hsq ▸ hG
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F s.1 a (boundary (n + 1)).ι hF
  have hq : q ≫ η.app (s.1.obj (Fin.last (n + 1))) =
      (boundary (n + 1)).ι ≫ s.2.app (Fin.last (n + 1)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedSimplexCoefficient_map η s.1 a (boundary (n + 1)).ι hF hG).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_congr G s.1 _ _ _ _ hG hr hsq rfl).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedSimplexCoefficient_restrict_self G s (boundary (n + 1)).ι hr))
  let sq : CommSq q (boundary (n + 1)).ι
      (η.app (s.1.obj (Fin.last (n + 1)))) (s.2.app (Fin.last (n + 1))) := ⟨hq⟩
  have : HasLiftingProperty (boundary (n + 1)).ι
      (η.app (s.1.obj (Fin.last (n + 1)))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := η.app (s.1.obj (Fin.last (n + 1)))) _ inferInstance
  obtain ⟨ψ, hψ, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_weightedBoundary_lift_with_coefficient F s.1 a hF
    sq.lift sq.fac_left
  refine ⟨SSet.yonedaEquiv.symm (⟨s.1, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1)), hψ, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  change (⟨s.1, ψ ≫ Functor.whiskerLeft s.1 η⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G (n + 1)) = s
  have he : ψ ≫ Functor.whiskerLeft s.1 η = s.2 := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDiagram_eq_of_boundary_and_last G s.1 _ s.2
    · change (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap η).app (Opposite.op ⦋n + 1⦌))
          (⟨s.1, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1))) = _
      rw [← SSet.yonedaEquiv_symm_comp, ← Category.assoc, hψ, hsq]
      exact congrArg (fun t ↦ (boundary (n + 1)).ι ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve G)).symm t) (Sigma.eta s).symm
    · change ψ.app (Fin.last (n + 1)) ≫ η.app _ = _
      rw [ht]
      exact sq.fac_right
  exact (congrArg (fun t ↦ (⟨s.1, t⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex G (n + 1))) he).trans
    (Sigma.eta s)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
