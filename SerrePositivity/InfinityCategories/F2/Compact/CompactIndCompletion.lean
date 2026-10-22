module

public import SerrePositivity.InfinityCategories.F2.Compact.CompactIndEquivalence

/-!
概要：元の compact Ind-Yoneda は冪等完備化であり、通常の Ind の compact 部分は Idem。
方針：元の全部分包含の充満忠実性と実際の Yoneda retract の回収を合わせる。
規約：元の全 Yoneda・比較・元の対象を保持。正則 κ と通常の ℵ₀ の場合を提供する。
使われ方：F2N-4(e) の実比較と、冪等完備化の全関手 ∞ 圏の普遍性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の compact Ind-Yoneda 自身は全写像空間で充満忠実。 -/
lemma compactIndYoneda_isFullyFaithful (κ : Cardinal.{u}) :
    IsFullyFaithful (compactIndYoneda κ C) := by
  apply (kappaCompactInclusion_isFullyFaithful.{u, u + 1} κ (Ind.IndInfinity κ C)).cancel_right
  rw [compactIndYoneda_inclusion]
  exact Ind.indYoneda_isFullyFaithful κ C

/-- 正則 κ について、元の compact Ind-Yoneda 自身が冪等完備化。 -/
lemma compactIndYoneda_isIdempotentCompletion (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    Idempotent.IsIdempotentCompletion (compactIndYoneda κ C) := by
  refine ⟨compactInd_isIdempotentComplete κ C, compactIndYoneda_isFullyFaithful κ, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := compactInd_retract_yoneda κ y
  exact ⟨ULift.up x, hx⟩

/-- 通常の Ind(C) の compact 部分と Idem(C) の、元の比較を順方向とする実同値。 -/
def compactIndOmegaEquivalence :
    QCatEquivalence (Idempotent.Idem C)
      (kappaCompactObjects.{u, u + 1} Cardinal.aleph0 (Ind.IndInfinity Cardinal.aleph0 C)) := by
  have : Fact (Cardinal.aleph0.{u}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  exact compactIndEquivalence Cardinal.aleph0

end SerrePositivity.InfinityCategories.F2.Compact
