module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFixedRightPrism

/-!
概要：二段の固定した終端収縮から単射の right anodyne 性を得る。
方針：right fibration に対する持ち上げ問題を、終端から二つの prism に沿って順に戻す。
規約：二つのホモトピーを単一の区間の射と同一視しない。
使われ方：内側ホーンを含む右ホーンの終点 fiber の包含の判定。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：部分を固定した二段の恒等射から retract への収縮を持つ単射は right anodyne。
方針：任意の right fibration に対する持ち上げを終端で作り、二段の相対 prism で補正する。
規約：J₀ は恒等から L、J₁ は L から r≫i。両方が i の像を全時間で固定する。
使われ方：右ホーン上の終点への二段収縮の持ち上げ。 -/
lemma rightAnodyneExtensions_of_fixed_terminal_homotopies {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (r : B ⟶ A) (hir : i ≫ r = 𝟙 A) (L : B ⟶ B)
    (J₀ J₁ : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
    (h₀₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ J₀ = 𝟙 B)
    (h₀₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ J₀ = L)
    (h₁₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ J₁ = L)
    (h₁₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ J₁ = r ≫ i)
    (hfix₀ : (Δ[1] ◁ i) ≫ J₀ = snd (Δ[1] : SSet.{u}) A ≫ i)
    (hfix₁ : (Δ[1] ◁ i) ≫ J₁ = snd (Δ[1] : SSet.{u}) A ≫ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i := by
  intro X Z p hp
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := ⟨hp⟩
  constructor
  intro a b hs
  let G := snd (Δ[1] : SSet.{u}) A ≫ a
  have hG (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
      (hf : (Δ[1] ◁ i) ≫ J = snd (Δ[1] : SSet.{u}) A ≫ i) :
      G ≫ p = (Δ[1] ◁ i) ≫ (J ≫ b) := by
    change (snd (Δ[1] : SSet.{u}) A ≫ a) ≫ p = _
    rw [Category.assoc, hs.w, ← Category.assoc, ← Category.assoc, hf]
  have hlast : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ G = i ≫ (r ≫ a) := by
    change a = i ≫ r ≫ a
    rw [← Category.assoc, hir, Category.id_comp]
  have hβ₁ : (r ≫ a) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ (J₁ ≫ b) := by
    rw [← Category.assoc, h₁₁]
    simpa only [Category.assoc] using congrArg (fun k ↦ r ≫ k) hs.w
  obtain ⟨H₁, hH₁fix, hH₁end, hH₁p⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightFibration_lift_fixed_prism i p G (r ≫ a) (J₁ ≫ b) hlast (hG J₁ hfix₁) hβ₁
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H₁
  have hF : F ≫ p = L ≫ b := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H₁) ≫ p = _
    rw [Category.assoc, hH₁p, ← Category.assoc, h₁₀]
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ G = i ≫ F := by
    change a = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H₁
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hH₁fix]
    rfl
  have hβ₀ : F ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ (J₀ ≫ b) := by
    rw [hF, ← Category.assoc, h₀₁]
  obtain ⟨H₀, hH₀fix, hH₀end, hH₀p⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightFibration_lift_fixed_prism i p G F (J₀ ≫ b) hfirst (hG J₀ hfix₀) hβ₀
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H₀, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hH₀fix]
    rfl
  · rw [Category.assoc, hH₀p, ← Category.assoc, h₀₀, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
