module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCorner
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorBoundary
public import SerrePositivity.InfinityCategories.Stable.LastJoinEvaluation

/-!
概要：補間領域の余錐を元の全円柱へ比較する実際の射。
方針：二重余錐の右二点を潰す第一座標と、区間の終点への第二座標を束ねる。
規約：補間領域の全包含を厳密に回収。使われ方：射図式の filtered 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 二重余錐の最後の二点を、同じ一つの余錐点へ送る。 -/
def arrowInterpolationConeFold (A : SSet.{u}) :
    join (join A (Δ[0] : SSet.{u})) Δ[0] ⟶ join A Δ[0] :=
  (stableJoinAssociator A Δ[0] Δ[0]).hom ≫
    joinMap (𝟙 A) (stableLastJoinEvaluation 0)

/-- 二重余錐の折り畳みは、元の余錐全体では恒等射。 -/
lemma arrowInterpolationConeFold_inl (A : SSet.{u}) :
    joinInl (join A (Δ[0] : SSet.{u})) Δ[0] ≫
      arrowInterpolationConeFold A = 𝟙 (join A Δ[0]) := by
  rw [arrowInterpolationConeFold, ← Category.assoc, stableJoinAssociator_inl,
    ← joinMap_comp, Category.id_comp, stableLastJoinEvaluation_inl, joinMap_id]

/-- 補間領域の右余錐から元の全円柱への二座標の比較。 -/
def arrowInterpolationCocone (A : SSet.{u}) :
    join (arrowInterpolationCorner A) (Δ[0] : SSet.{u}) ⟶ join A Δ[0] ⊗ Δ[1] :=
  lift (joinMap (arrowInterpolationCornerInclusion A ≫ fst _ _) (𝟙 Δ[0]) ≫
      arrowInterpolationConeFold A)
    (joinMap (arrowInterpolationCornerInclusion A ≫ snd _ _) (𝟙 Δ[0]) ≫
      stableLastJoinEvaluation 1)

/-- 全補間領域上では、比較は元の全円柱への包含そのもの。 -/
lemma arrowInterpolationCocone_inl (A : SSet.{u}) :
    joinInl (arrowInterpolationCorner A) (Δ[0] : SSet.{u}) ≫
      arrowInterpolationCocone A = arrowInterpolationCornerInclusion A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [arrowInterpolationCocone, Category.assoc, lift_fst]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc,
      arrowInterpolationConeFold_inl, Category.comp_id]
  · simp only [arrowInterpolationCocone, Category.assoc, lift_snd]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc,
      stableLastJoinEvaluation_inl, Category.comp_id]

/-- 元の円柱全体の境界は厳密に保たれる。 -/
lemma arrowInterpolationCocone_old (A : SSet.{u}) :
    pushout.inl SSet.ι₀ (joinInl A (Δ[0] : SSet.{u})) ≫
      joinInl (arrowInterpolationCorner A) Δ[0] ≫ arrowInterpolationCocone A =
        joinInl A Δ[0] ▷ (Δ[1] : SSet.{u}) := by
  rw [arrowInterpolationCocone_inl, arrowInterpolationCornerInclusion_old]

/-- 新しい始点余錐全体の境界も厳密に保たれる。 -/
lemma arrowInterpolationCocone_source (A : SSet.{u}) :
    pushout.inr SSet.ι₀ (joinInl A (Δ[0] : SSet.{u})) ≫
      joinInl (arrowInterpolationCorner A) Δ[0] ≫ arrowInterpolationCocone A =
        (SSet.ι₀ : join A Δ[0] ⟶ join A Δ[0] ⊗ Δ[1]) := by
  rw [arrowInterpolationCocone_inl, arrowInterpolationCornerInclusion_source]

end SerrePositivity.InfinityCategories.F2.Ind
