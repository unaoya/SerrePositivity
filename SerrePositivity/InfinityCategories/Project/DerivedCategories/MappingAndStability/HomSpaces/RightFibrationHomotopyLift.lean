module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RoofRightPrismLift
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 右ファイブレーション上の終端指定ホモトピー

概要：指定終端図式とその底のホモトピーを、同じ全時間の底を保って持ち上げる。
方針：区間因子を入れ替えて終端固定 prism を持ち上げ、元の区間順へ戻す。
規約：底と終端を厳密に保つ。使われ方：有限対充填の slice 引き戻しへの移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 右ファイブレーションは指定終端から底のホモトピー全体を持ち上げる。 -/
lemma rightFibration_lift_end_homotopy {K Y Q : SSet.{u}} (p : Y ⟶ Q) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (u : K ⟶ Y) {f g : K ⟶ Q} (H : SSet.Homotopy f g) (hu : u ≫ p = g) :
    ∃ v : K ⟶ Y, ∃ T : SSet.Homotopy v u, v ≫ p = f ∧ T.h ≫ p = H.h := by
  let β := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  have hb : u ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ β := by
    dsimp only [β]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, H.h₁]
    exact hu
  obtain ⟨G, hG₁, hGp⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.roofRightFibration_lift_end_prism p u β hb
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ G
  let T : SSet.Homotopy v u := {
    h := (β_ K (Δ[1] : SSet.{u})).hom ≫ G
    h₀ := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ G = v; rfl
    h₁ := by change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ G = u; exact hG₁
    rel := by ext n s; exact False.elim s.1.property }
  have hT : T.h ≫ p = H.h := by
    change ((β_ K Δ[1]).hom ≫ G) ≫ p = _
    rw [Category.assoc, hGp]
    dsimp only [β]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  refine ⟨v, T, ?_, hT⟩
  rw [← T.h₀, Category.assoc, hT, H.h₀]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
