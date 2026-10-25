module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSuccessorDiagram

/-!
概要：次の全比較図式に、元の大域余錐を保持する増大余錐を付ける。
方針：二重 coslice による一頂点延長を小さい余錐形状へ正規化する。
規約：旧全形状と右側の元の余錐の全制限を厳密に保持する。
使われ方：左右交互比較の後続状態。
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
variable {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}

/-- 指定因子化辺から次の全比較の増大余錐を作る。 -/
def comparisonSuccessorAugmentation {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) : JoinCocone (comparisonSuccessorDiagram f) :=
  (sequentialCoconeExtension f.edge).restrict (uliftCoconeShapeIso.{u, u + 1} s.shape 0).hom

/-- 次の増大余錐の頂点は、元の同じ大域余錐の頂点を保持する。 -/
lemma comparisonSuccessorAugmentation_vertex {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    (comparisonSuccessorAugmentation f).vertex = s.augmentation.vertex := by
  rw [comparisonSuccessorAugmentation, JoinCocone.vertex_restrict,
    sequentialCoconeExtension_vertex]

/-- 次の増大余錐の旧全形状への制限は、元の同じ増大余錐である。 -/
lemma comparisonSuccessorAugmentation_old_val {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    ((comparisonSuccessorAugmentation f).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl s.shape Δ[0]))).val =
        s.augmentation.val := by
  change joinMap _ (𝟙 Δ[0]) ≫ (joinMap _ (𝟙 Δ[0]) ≫
    (sequentialCoconeExtension f.edge).val) = _
  rw [← Category.assoc, ← joinMap_comp, uliftCoconeShapeIso_inl, Category.id_comp]
  exact sequentialCoconeExtension_restrict_val f.edge

/-- 右側の元の全余錐は、次の増大余錐の中に厳密に残る。 -/
lemma comparisonSuccessorAugmentation_right {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    ((comparisonSuccessorAugmentation f).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map
        (s.right_inclusion ≫ joinInl s.shape Δ[0]))).val =
      (c₁.restrict ((SSet.uliftFunctor.{u + 1, u}).map s.right_index)).val := by
  have hj : joinMap ((SSet.uliftFunctor.{u + 1, u}).map s.right_inclusion ≫
        (SSet.uliftFunctor.{u + 1, u}).map (joinInl s.shape Δ[0])) (𝟙 Δ[0]) =
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map s.right_inclusion) (𝟙 Δ[0]) ≫
        joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInl s.shape Δ[0])) (𝟙 Δ[0]) := by
    simpa only [Category.id_comp] using joinMap_comp
      ((SSet.uliftFunctor.{u + 1, u}).map s.right_inclusion)
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl s.shape Δ[0])) (𝟙 Δ[0]) (𝟙 Δ[0])
  change joinMap _ _ ≫ (comparisonSuccessorAugmentation f).val = _
  rw [(SSet.uliftFunctor.{u + 1, u}).map_comp, hj, Category.assoc]
  have ho := comparisonSuccessorAugmentation_old_val f
  change joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInl s.shape Δ[0])) (𝟙 Δ[0]) ≫
    (comparisonSuccessorAugmentation f).val = s.augmentation.val at ho
  rw [ho]
  exact s.right_augmentation

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
