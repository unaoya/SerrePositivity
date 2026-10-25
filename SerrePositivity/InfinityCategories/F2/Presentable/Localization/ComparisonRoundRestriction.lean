module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonRounds

/-!
概要：左右一巡の前後で、元の全図式・全余錐・両添字図式の制限を保持する。
方針：一頂点延長を二回合成し、各段の厳密な旧形状制限を使う。
規約：全高次成分の等式。使われ方：可算交互列を全図式へ貼り合わせる準備。
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

/-- 後続の全図式を旧全形状へ制限すると元の全図式に戻る。 -/
lemma comparisonSuccessorDiagram_old {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl s.shape Δ[0]) ≫
      comparisonSuccessorDiagram f = s.diagram := by
  rw [comparisonSuccessorDiagram, ← Category.assoc, uliftCoconeShapeIso_inl, f.cocone.property]

variable {hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))}
  {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}

/-- 一巡前の全形状を一巡後の全形状に入れる指定包含。 -/
def ComparisonRound.inclusion (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    s.shape ⟶ (r.next hD₁).shape :=
  joinInl s.shape Δ[0] ≫ joinInl (join s.shape Δ[0]) Δ[0]

/-- 一巡の指定包含は全次数で単射である。 -/
lemma ComparisonRound.inclusion_mono (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    Mono (r.inclusion hD₁) := by
  dsimp only [ComparisonRound.inclusion]
  infer_instance

/-- 一巡後の全図式を旧全形状へ制限すると元の同じ全図式である。 -/
lemma ComparisonRound.diagram_restrict (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    (SSet.uliftFunctor.{u + 1, u}).map (r.inclusion hD₁) ≫ (r.next hD₁).diagram =
      s.diagram := by
  change (SSet.uliftFunctor.{u + 1, u}).map
    (joinInl s.shape Δ[0] ≫ joinInl (join s.shape Δ[0]) Δ[0]) ≫
      comparisonSuccessorDiagram r.right = _
  rw [(SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc]
  erw [comparisonSuccessorDiagram_old r.right, comparisonSuccessorDiagram_old r.left]

/-- 左側の一巡後の添字余錐は、旧全前置図式上で元の添字に戻る。 -/
lemma ComparisonRound.left_index_restrict (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    joinInl s.left_shape Δ[0] ≫ (r.next hD₁).left_index = s.left_index :=
  r.left.index.property

/-- 右側についても元の全前置添字を厳密に保持する。 -/
lemma ComparisonRound.right_index_restrict (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    joinInl s.right_shape Δ[0] ≫ (r.next hD₁).right_index = s.right_index :=
  r.right.index.property

/-- 一巡後の大域余錐を旧全形状へ制限しても、元の全余錐が厳密に残る。 -/
lemma ComparisonRound.augmentation_restrict_val (r : ComparisonRound hD₀ s)
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i))) :
    (((r.next hD₁).augmentation).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (r.inclusion hD₁))).val =
        s.augmentation.val := by
  change joinMap ((SSet.uliftFunctor.{u + 1, u}).map
    (joinInl s.shape Δ[0] ≫ joinInl (join s.shape Δ[0]) Δ[0])) (𝟙 Δ[0]) ≫
      (comparisonSuccessorAugmentation r.right).val = _
  rw [(SSet.uliftFunctor.{u + 1, u}).map_comp]
  change joinMap _ (𝟙 Δ[0] ≫ 𝟙 Δ[0]) ≫ _ = _
  rw [joinMap_comp, Category.assoc]
  have h₁ := comparisonSuccessorAugmentation_old_val r.right
  have h₀ := comparisonSuccessorAugmentation_old_val r.left
  change joinMap _ (𝟙 Δ[0]) ≫ (comparisonSuccessorAugmentation r.right).val =
    (comparisonSuccessorAugmentation r.left).val at h₁
  change joinMap _ (𝟙 Δ[0]) ≫ (comparisonSuccessorAugmentation r.left).val =
    s.augmentation.val at h₀
  erw [h₁, h₀]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
