module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RoofRightPrismLift

/-! # 屋根比較の相対問題の同時 prism 輸送

概要：境界の元屋根と全体の商屋根を、同じ底の prism に沿って厳密に整合させて輸送する。
方針：元の境界を先に右持ち上げし、その比較像を固定して商の全体を相対持ち上げする。
規約：二つの射影は右ファイブレーション。使われ方：相対充填問題の共通 fiber への還元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {A K E Q B : SSet.{u}} (i : A ⟶ K) (p : E ⟶ B) (q : Q ⟶ B)
variable (F : E ⟶ Q) (a : A ⟶ E) (g : K ⟶ Q) (β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)

/-- 元の境界と商の全体を厳密に揃えた、全底付きの二つの輸送 prism。 -/
structure RoofRelativeFiberPrism where
  source : (Δ[1] : SSet.{u}) ⊗ A ⟶ E
  target : (Δ[1] : SSet.{u}) ⊗ K ⟶ Q
  source_end : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ source = a
  target_end : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ target = g
  source_over : source ≫ p = (Δ[1] ◁ i) ≫ β
  target_over : target ≫ q = β
  boundary : (Δ[1] ◁ i) ≫ target = source ≫ F

/-- 二つの右ファイブレーションの比較に沿う相対問題は同じ底の prism で輸送できる。 -/
theorem roofRelativeFiberPrism_nonempty [Mono i] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q]
    (hF : F ≫ q = p) (ha : a ≫ F = i ≫ g)
    (hβ : g ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ β) :
    Nonempty (RoofRelativeFiberPrism i p q F a g β) := by
  have hA : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ ((Δ[1] ◁ i) ≫ β) := by
    rw [← hF, ← Category.assoc, ha, Category.assoc, hβ]
    simpa only [Category.assoc] using
      (congrArg (fun r => r ≫ β) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 1 i)).symm
  obtain ⟨H, hHend, hHp⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.roofRightFibration_lift_end_prism p a ((Δ[1] ◁ i) ≫ β) hA
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ (H ≫ F) = i ≫ g := by
    rw [← Category.assoc, hHend, ha]
  have hHq : (H ≫ F) ≫ q = (Δ[1] ◁ i) ≫ β := by
    rw [Category.assoc, hF, hHp]
  obtain ⟨J, hJboundary, hJend, hJq⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightFibration_lift_fixed_prism i q (H ≫ F) g β h₁ hHq hβ
  exact ⟨⟨H, J, hHend, hJend, hHp, hJq, hJboundary⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
