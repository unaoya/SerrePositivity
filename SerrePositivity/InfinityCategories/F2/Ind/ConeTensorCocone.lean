module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCorner
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeCoordinates

/-!
概要：一般の補間領域への余錐を、元の二つの余錐の積へ比較する。
方針：既存の二重余錐の折り畳みを両座標へ適用する。
規約：元の全境界と新しい二つの余錐点を厳密に保持する。
使われ方：有限半順序形状の点追加における全補間の形状比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：補間領域への余錐から元の余錐の積への全比較。
方針：両座標の折り畳み。規約：全射の等号。使われ方：境界と頂点の回収。 -/
def coneTensorCocone (A L : SSet.{u}) :
    join (coneTensorCorner A L) (Δ[0] : SSet.{u}) ⟶ join A Δ[0] ⊗ join L Δ[0] :=
  lift (joinMap (coneTensorCornerInclusion A L ≫ fst _ _) (𝟙 Δ[0]) ≫
      arrowInterpolationConeFold A)
    (joinMap (coneTensorCornerInclusion A L ≫ snd _ _) (𝟙 Δ[0]) ≫
      arrowInterpolationConeFold L)
/-- 概要：全補間領域への制限は元の包含そのもの。
方針：両座標の折り畳み。規約：全射の等号。使われ方：境界と頂点の回収。 -/
lemma coneTensorCocone_inl (A L : SSet.{u}) :
    joinInl (coneTensorCorner A L) (Δ[0] : SSet.{u}) ≫
      coneTensorCocone A L = coneTensorCornerInclusion A L := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [coneTensorCocone, Category.assoc, lift_fst]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc,
      arrowInterpolationConeFold_inl, Category.comp_id]
  · simp only [coneTensorCocone, Category.assoc, lift_snd]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc,
      arrowInterpolationConeFold_inl, Category.comp_id]
/-- 概要：比較の余錐点は元の二つの指定余錐点。
方針：両座標の折り畳み。規約：全射の等号。使われ方：境界と頂点の回収。 -/
lemma coneTensorCocone_inr (A L : SSet.{u}) :
    joinInr (coneTensorCorner A L) (Δ[0] : SSet.{u}) ≫ coneTensorCocone A L =
      lift (joinInr A (Δ[0] : SSet.{u})) (joinInr L Δ[0]) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [coneTensorCocone, Category.assoc, lift_fst]
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp,
      arrowInterpolationConeFold_inr]
  · simp only [coneTensorCocone, Category.assoc, lift_snd]
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp,
      arrowInterpolationConeFold_inr]

end SerrePositivity.InfinityCategories.F2.Ind
