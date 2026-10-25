module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSuccessorAugmentation
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonLeftCoconeFaces
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.JoinAssociatorComparison

/-!
概要：P-13 の公開比較で、次の全比較の左側の全増大余錐を接続する。
方針：元の因子化辺の射影、二重 coslice の自然性、元の表示余錐脚の全式を使う。
規約：結合同型の比較は公開葉を読み取り専用で使う。使われ方：交互後続状態の完成。
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

/-- 元の因子化辺を左前置形状へ制限して延長すると、元の表示の全後続余錐になる。 -/
lemma comparisonSuccessorAugmentation_left_raw {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    joinMap (joinMap ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion) (𝟙 Δ[0]))
      (𝟙 Δ[0]) ≫ (sequentialCoconeExtension f.edge).val =
    joinMap (((uliftSliceUnderIso.{u, u + 1} s.left_index).hom).app _ (ULift.up f.index)).val
      (𝟙 Δ[0]) ≫ c₀.val := by
  rw [sequentialCoconeExtension_restrict_naturality, sequentialCoconeExtension_val,
    stableJoinAssociator_hom_eq_joinAssociator_point_point, f.projection]
  exact comparisonLeftCocone_leg_uncurry s f.index

/-- 次の全比較の左側の増大余錐は、元の同じ左表示の全余錐を厳密に保つ。 -/
lemma comparisonSuccessorAugmentation_left {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    ((comparisonSuccessorAugmentation f).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (joinMap s.left_inclusion (𝟙 Δ[0])))).val =
      (c₀.restrict ((SSet.uliftFunctor.{u + 1, u}).map f.index.val)).val := by
  change joinMap _ (𝟙 Δ[0]) ≫ (joinMap _ (𝟙 Δ[0]) ≫
    (sequentialCoconeExtension f.edge).val) = _
  rw [← Category.assoc, ← joinMap_comp, uliftCoconeShapeIso_left_naturality]
  change joinMap ((uliftCoconeShapeIso.{u, u + 1} s.left_shape 0).hom ≫
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion) (𝟙 Δ[0]))
      (𝟙 Δ[0] ≫ 𝟙 Δ[0]) ≫ (sequentialCoconeExtension f.edge).val = _
  rw [joinMap_comp, Category.assoc, comparisonSuccessorAugmentation_left_raw,
    uliftSliceUnderIso_hom_val]
  rw [← Category.assoc, ← joinMap_comp, Iso.hom_inv_id_assoc, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
