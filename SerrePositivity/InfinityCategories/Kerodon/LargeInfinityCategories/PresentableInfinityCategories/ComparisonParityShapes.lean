module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonSequence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonRoundFaces

/-!
概要：二表示の全比較列の左右の前置包含を、偶数・奇数の標準面として回収する。
方針：全形状と両前置形状の同型を同じ再帰で延ばし、一巡の全可換式を使う。
規約：初期全形状は標準辺、両前置形状は標準点。使われ方：共通部分表示の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}
variable (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₀]
  [Quasicategory I₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₁]
  (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁)

/-- 初期全辺を延ばして得る、全比較の奇数次数の標準単体表示。 -/
def comparisonSequenceParityShapeIso (e₀ : s₀.shape ≅ (Δ[1] : SSet.{u})) : ∀ n,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape ≅ (Δ[2 * n + 1] : SSet.{u}) :=
  Nat.rec (motive := fun n ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape ≅ (Δ[2 * n + 1] : SSet.{u})) e₀
    (fun n e ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).simplexShapeIso hD₁ e)

/-- 左の初期点から得る、左全前置形状の標準単体表示。 -/
def comparisonSequenceLeftParityShapeIso (l₀ : s₀.left_shape ≅ (Δ[0] : SSet.{u})) : ∀ n,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape ≅ (Δ[n] : SSet.{u}) :=
  Nat.rec (motive := fun n ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape ≅ (Δ[n] : SSet.{u})) l₀
    (fun _ e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oneConeSimplexIso e)

/-- 右の初期点から得る、右全前置形状の標準単体表示。 -/
def comparisonSequenceRightParityShapeIso (l₀ : s₀.right_shape ≅ (Δ[0] : SSet.{u})) : ∀ n,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape ≅ (Δ[n] : SSet.{u}) :=
  Nat.rec (motive := fun n ↦
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape ≅ (Δ[n] : SSet.{u})) l₀
    (fun _ e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oneConeSimplexIso e)

/-- 左側の元の全前置包含は、全比較の偶数面そのものである。 -/
lemma comparisonSequence_left_parity_face
    (e₀ : s₀.shape ≅ (Δ[1] : SSet.{u})) (l₀ : s₀.left_shape ≅ (Δ[0] : SSet.{u}))
    (h₀ : s₀.left_inclusion ≫ e₀.hom = l₀.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace 0) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_inclusion ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace n := by
  induction n with
  | zero => exact h₀
  | succ n hn =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_face_successor hD₁
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace (n + 1)) hn (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace_succ_join n)

/-- 右側の元の全前置包含は、全比較の奇数面そのものである。 -/
lemma comparisonSequence_right_parity_face
    (e₀ : s₀.shape ≅ (Δ[1] : SSet.{u})) (l₀ : s₀.right_shape ≅ (Δ[0] : SSet.{u}))
    (h₀ : s₀.right_inclusion ≫ e₀.hom = l₀.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace 0) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_inclusion ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace n := by
  induction n with
  | zero => exact h₀
  | succ n hn =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_face_successor hD₁
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace (n + 1)) hn (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace_succ_join n)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
