module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSuccessorLeftAugmentation
public import SerrePositivity.InfinityCategories.F1.Joins.JoinQuasicategory
public import SerrePositivity.InfinityCategories.F2.Ind.ConeApexTerminal
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.SmallJoin

/-!
概要：二つの元の表示・全余錐を保持する、compact 全前置比較の後続状態を作る。
方針：元の相対因子化の余錐を加え、公開 P-13 で両側の全増大余錐を接続する。
規約：後続状態の存在を新しい仮定にしない。使われ方：左右交互の再帰。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}

/-- 左側の元の表示に沿って全前置比較を一段延長する。 -/
def comparisonLeftSuccessor {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s)
    (hD : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))) :
    CompactPresentationComparison μ D₀ D₁ c₀ c₁ where
  shape := join s.shape Δ[0]
  shape_quasicategory := by
    have := s.shape_quasicategory
    infer_instance
  shape_small := isKappaSmall_join (Fact.out : μ.IsRegular) s.shape_small
    (isKappaSmall_of_finite (Fact.out : μ.IsRegular).aleph0_le _)
  diagram := comparisonSuccessorDiagram f
  compact := comparisonSuccessorDiagram_compact f hD
  augmentation := comparisonSuccessorAugmentation f
  left_shape := join s.left_shape Δ[0]
  left_quasicategory := by
    have := s.left_quasicategory
    infer_instance
  left_small := isKappaSmall_join (Fact.out : μ.IsRegular) s.left_small
    (isKappaSmall_of_finite (Fact.out : μ.IsRegular).aleph0_le _)
  left_terminal := Ind.coneApex s.left_shape
  left_isTerminal := Ind.coneApex_isTerminalVertex s.left_shape
  left_index := f.index.val
  left_inclusion := joinMap s.left_inclusion (𝟙 Δ[0])
  left_mono := by
    have := s.left_mono
    infer_instance
  left_diagram := comparisonSuccessorDiagram_left f
  left_augmentation := comparisonSuccessorAugmentation_left f
  right_shape := s.right_shape
  right_quasicategory := s.right_quasicategory
  right_small := s.right_small
  right_terminal := s.right_terminal
  right_isTerminal := s.right_isTerminal
  right_index := s.right_index
  right_inclusion := s.right_inclusion ≫ joinInl s.shape Δ[0]
  right_mono := by
    have := s.right_mono
    infer_instance
  right_diagram := comparisonSuccessorDiagram_right f
  right_augmentation := comparisonSuccessorAugmentation_right f

/-- 右側の元の表示に沿う延長は、同じ構成を左右交換して戻すことで得る。 -/
def comparisonRightSuccessor {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s.swap)
    (hD : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    CompactPresentationComparison μ D₀ D₁ c₀ c₁ :=
  (comparisonLeftSuccessor f hD).swap

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
