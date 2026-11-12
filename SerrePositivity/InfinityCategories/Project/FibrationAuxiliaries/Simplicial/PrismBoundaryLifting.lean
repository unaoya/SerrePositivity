module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.PrismBoundaryRecovery

/-!
概要：二端点と底を指定した prism のパラメーターに関する相対持ち上げ。
方針：区間境界の相対内部 Hom の持ち上げを実際の prism に展開する。
規約：既定の部分、二端点、底を全て厳密に保つ。
使われ方：全 lift prism 空間の同時端点制限の充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 概要：相対内部 Hom の持ち上げから二端点を固定した prism の相対延長を得る。
方針：二端点と底を相対データに束ね、持ち上げを評価する。
規約：i は任意で必要な持ち上げ性を明示する。
使われ方：同時端点制限の左ホーンの充填。 -/
lemma exists_prismBoundaryLift {E B K L M : SSet.{u}} (p : E ⟶ B)
    (r : internalHom.PullbackObjObj ((boundary 1).ι ▷ K) p)
    (i : M ⟶ L) [HasLiftingProperty i r.π]
    (v₀ v₁ : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (h₀ : v₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ)
    (h₁ : v₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ δ)
    (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (H₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = (K ◁ i) ≫ v₀)
    (H₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = (K ◁ i) ≫ v₁)
    (Hp : H ≫ p = (Δ[1] ◁ (K ◁ i)) ≫ δ) :
    ∃ F : Δ[1] ⊗ (K ⊗ L) ⟶ E,
      (Δ[1] ◁ (K ◁ i)) ≫ F = H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ F = v₀ ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ F = v₁ ∧ F ≫ p = δ := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData p r v₀ v₁ δ h₀ h₁
  have hc : curry ((α_ Δ[1] K M).hom ≫ H) ≫ r.π = i ≫ d := by
    dsimp only [d]
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_precomp]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_eq_of_prism p r _ _ _ _ _ H H₀ H₁ Hp).symm
  let sq : CommSq (curry ((α_ Δ[1] K M).hom ≫ H)) i r.π d := ⟨hc⟩
  let F := (α_ Δ[1] K L).inv ≫ uncurry sq.lift
  have hboundary := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_recover_boundary p r v₀ v₁ δ h₀ h₁
    sq.lift sq.fac_right
  refine ⟨F, ?_, ?_, ?_, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.prismBoundaryData_recover_base p r v₀ v₁ δ h₀ h₁
    sq.lift sq.fac_right⟩
  · calc
      _ = (α_ Δ[1] K M).inv ≫ uncurry (i ≫ sq.lift) := by
        rw [uncurry_natural_left]
        rfl
      _ = H := by rw [sq.fac_left, uncurry_curry, Iso.inv_hom_id_assoc]
  · have h := congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 (K ⊗ L) ≫ w) hboundary
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero] at h
    exact h
  · have h := congrArg (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 (K ⊗ L) ≫ w) hboundary
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one] at h
    exact h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
