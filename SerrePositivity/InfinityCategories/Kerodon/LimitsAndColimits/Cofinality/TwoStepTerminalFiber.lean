module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TwoStepTerminalAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalFiberCofinality

/-!
概要：二段の固定した終点収縮を持つ底上の left fibration の終点 fiber の包含。
方針：二つの収縮を fiber を固定して順に持ち上げ、二段の right anodyne 判定を使う。
規約：中間の自己射を明示する。底の quasicategory 性は不要。
使われ方：全ての右ホーンの引き戻しの比較。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：二段の固定した終点収縮があれば left fibration の fiber 包含は right anodyne。
方針：二つの相対 left prism の持ち上げから、全空間の固定した二段収縮を作る。
規約：全ての終点定値族を両方の収縮が固定する。
使われ方：右ホーンと標準単体の共通 fiber からの cofinality の消去。 -/
lemma leftFibration_terminalFiber_rightAnodyne_of_two_fixed_contractions
    {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (M : B ⟶ B)
    (C₀ C₁ : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
    (h₀₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ C₀ = 𝟙 B)
    (h₀₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ C₀ = M)
    (h₁₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ C₁ = M)
    (h₁₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ C₁ = SSet.const b)
    (hfix₀ : ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ C₀ = SSet.const b)
    (hfix₁ : ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ C₁ = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  let G := snd (Δ[1] : SSet.{u}) F ≫ i
  have hG (C : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
      (hf : ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ C = SSet.const b) :
      G ≫ p = (Δ[1] ◁ i) ≫ ((Δ[1] ◁ p) ≫ C) := by
    change (snd (Δ[1] : SSet.{u}) F ≫ i) ≫ p = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, hf]
  have hstart : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 F ≫ G = i ≫ 𝟙 E := by
    rw [Category.comp_id]
    rfl
  have hβ₀ : (𝟙 E) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ ((Δ[1] ◁ p) ≫ C₀) := by
    rw [Category.id_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      h₀₀, Category.comp_id]
  obtain ⟨H₀, hH₀fix, hH₀start, hH₀p⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_lift_fixed_prism i p G (𝟙 E) _ hstart (hG C₀ hfix₀) hβ₀
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H₀
  have hLp : L ≫ p = p ≫ M := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H₀) ≫ p = _
    rw [Category.assoc, hH₀p, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
      Category.assoc, h₀₁]
  have hmiddle : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 F ≫ G = i ≫ L := by
    change i = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H₀
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hH₀fix]
    rfl
  have hβ₁ : L ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ ((Δ[1] ◁ p) ≫ C₁) := by
    rw [hLp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h₁₀]
  obtain ⟨H₁, hH₁fix, hH₁start, hH₁p⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_lift_fixed_prism i p G L _ hmiddle (hG C₁ hfix₁) hβ₁
  let N := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H₁
  have hNp : N ≫ p = SSet.const b := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H₁) ≫ p = _
    rw [Category.assoc, hH₁p, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
      Category.assoc, h₁₁, SSet.comp_const]
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b N hNp
  have hir : i ≫ r = 𝟙 F := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    change i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H₁ = i
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hH₁fix]
    rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightAnodyneExtensions_of_fixed_terminal_homotopies i r hir L H₀ H₁
    hH₀start rfl hH₁start
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p b N hNp).symm
  · exact hH₀fix
  · exact hH₁fix

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
