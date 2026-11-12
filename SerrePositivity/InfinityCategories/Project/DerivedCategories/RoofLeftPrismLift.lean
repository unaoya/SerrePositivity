module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismBoundaryExtension

/-! # 左ファイブレーションの始端固定 prism 持ち上げ

概要：任意の底 prism を指定始端図式から全パラメータ付きで持ち上げる。
方針：終対象 slice の切断と left anodyne prism の持ち上げを接続する。
規約：モデル構造・有限性を仮定しない。使われ方：任意標的への屋根評価の全体構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
/-- 左ファイブレーションは、指定始端を厳密に保持して任意の底 prism を持ち上げる。 -/
lemma roofLeftFibration_lift_start_prism {K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : K ⟶ E)
    (β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (hβ : f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ H = f ∧ H ≫ p = β := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_point_whiskerRight K p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))
  have sq : CommSq (snd (horn 1 0 : SSet.{u}) K ≫ f) ((horn 1 0).ι ▷ K) p β := by
    constructor
    rw [Category.assoc, hβ, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization]
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  have h := congrArg (fun g => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection K ≫ g) sq.fac_left
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
    Category.id_comp] using h


end SerrePositivity.InfinityCategories.Project.DerivedCategories
