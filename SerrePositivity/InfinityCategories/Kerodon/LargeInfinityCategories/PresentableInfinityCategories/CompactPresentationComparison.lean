module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativePrefixPresentationFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialCoconeNaturality

/-!
概要：二つの元の filtered 表示を保つ、compact な全前置比較の状態を記録する。
方針：両側の小さい終前置図式と全増大余錐の整合を、元の全射の等式で保持する。
規約：状態の存在や可算交互列の存在は定義へ仮定しない。
使われ方：HTT 5.5.4.13 の二つの表示を交互に延長する再帰。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 元の二表示の全前置図式と全余錐を保持する、比較の一段階。 -/
structure CompactPresentationComparison (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C)
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁) where
  shape : SSet.{u}
  shape_quasicategory : Quasicategory shape
  shape_small : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ shape
  diagram : (SSet.uliftFunctor.{u + 1, u}).obj shape ⟶ C
  compact : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (diagram.app _ v)
  augmentation : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone diagram
  left_shape : SSet.{u}
  left_quasicategory : Quasicategory left_shape
  left_small : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ left_shape
  left_terminal : left_shape _⦋0⦌
  left_isTerminal : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex left_terminal
  left_index : left_shape ⟶ I₀
  left_inclusion : left_shape ⟶ shape
  left_mono : Mono left_inclusion
  left_diagram : (SSet.uliftFunctor.{u + 1, u}).map left_inclusion ≫ diagram =
    (SSet.uliftFunctor.{u + 1, u}).map left_index ≫ D₀
  left_augmentation : (augmentation.restrict
    ((SSet.uliftFunctor.{u + 1, u}).map left_inclusion)).val =
      (c₀.restrict ((SSet.uliftFunctor.{u + 1, u}).map left_index)).val
  right_shape : SSet.{u}
  right_quasicategory : Quasicategory right_shape
  right_small : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ right_shape
  right_terminal : right_shape _⦋0⦌
  right_isTerminal : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex right_terminal
  right_index : right_shape ⟶ I₁
  right_inclusion : right_shape ⟶ shape
  right_mono : Mono right_inclusion
  right_diagram : (SSet.uliftFunctor.{u + 1, u}).map right_inclusion ≫ diagram =
    (SSet.uliftFunctor.{u + 1, u}).map right_index ≫ D₁
  right_augmentation : (augmentation.restrict
    ((SSet.uliftFunctor.{u + 1, u}).map right_inclusion)).val =
      (c₁.restrict ((SSet.uliftFunctor.{u + 1, u}).map right_index)).val

namespace CompactPresentationComparison
variable {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}

/-- 二つの元の表示を交換しても同じ比較図式と全余錐を保持する。 -/
def swap (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    CompactPresentationComparison μ D₁ D₀ c₁ c₀ where
  shape := s.shape
  shape_quasicategory := s.shape_quasicategory
  shape_small := s.shape_small
  diagram := s.diagram
  compact := s.compact
  augmentation := s.augmentation
  left_shape := s.right_shape
  left_quasicategory := s.right_quasicategory
  left_small := s.right_small
  left_terminal := s.right_terminal
  left_isTerminal := s.right_isTerminal
  left_index := s.right_index
  left_inclusion := s.right_inclusion
  left_mono := s.right_mono
  left_diagram := s.right_diagram
  left_augmentation := s.right_augmentation
  right_shape := s.left_shape
  right_quasicategory := s.left_quasicategory
  right_small := s.left_small
  right_terminal := s.left_terminal
  right_isTerminal := s.left_isTerminal
  right_index := s.left_index
  right_inclusion := s.left_inclusion
  right_mono := s.left_mono
  right_diagram := s.left_diagram
  right_augmentation := s.left_augmentation

/-- 左右を二回交換すると、元の同じ状態に戻る。 -/
lemma swap_swap (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) : s.swap.swap = s := rfl

/-- 左側の全余錐の整合は、元の表示の大域頂点も厳密に保持する。 -/
lemma vertex_left (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    s.augmentation.vertex = c₀.vertex := by
  have h := congrArg (fun f ↦ SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{u + 1, u}).obj s.left_shape) Δ[0] ≫ f))
      s.left_augmentation
  change (s.augmentation.restrict _).vertex = (c₀.restrict _).vertex at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict] using h

/-- 右側の元の表示についても、同じ大域頂点を保持する。 -/
lemma vertex_right (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    s.augmentation.vertex = c₁.vertex := s.swap.vertex_left

end CompactPresentationComparison
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
