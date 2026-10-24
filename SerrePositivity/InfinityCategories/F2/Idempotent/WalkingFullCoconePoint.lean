module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingFullCocone
public import SerrePositivity.InfinityCategories.F2.Idempotent.PointJoinNerveExt

/-!
概要：元の全余錐を元の分裂対象の一点へ制限すると、元の定値な一点余錐になる。
方針：nerve への全写像を一次単体で判定し、両境界と元の恒等脚を照合する。
規約：元の一点包含と元の全余錐をそのまま制限する。
使われ方：任意の quasicategory への像で元の余錐の余極限性を証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全余錐の終対象への一点制限は、元の分裂対象への定値な全写像。 -/
lemma walkingFullJoinCocone_point_restrict :
    joinMap (nervePoint walkingImage) (𝟙 (Δ[0] : SSet.{u})) ≫ walkingFullJoinCocone.val =
      SSet.const (nerveVertex walkingImage) := by
  let f := joinMap (nervePoint walkingImage) (𝟙 (Δ[0] : SSet.{u})) ≫
    walkingFullJoinCocone.val
  let g : join (Δ[0] : SSet.{u}) Δ[0] ⟶ SplitShape := SSet.const (nerveVertex walkingImage)
  have he : nervePoint walkingImage =
      (SSet.const (nerveVertex walkingImage) : (Δ[0] : SSet.{u}) ⟶ SplitShape) := by
    rw [nervePoint, SSet.yonedaEquiv_symm_zero]
  have hl : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ f = joinInl _ _ ≫ g := by
    dsimp only [f, g]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc]
    have h := congrArg (fun q ↦ nervePoint walkingImage ≫ q) walkingFullJoinCocone.property
    exact h.trans ((Category.comp_id _).trans (he.trans (SSet.comp_const _ _).symm))
  have hr : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ f = joinInr _ _ ≫ g := by
    dsimp only [f, g]
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    exact walkingFullJoinCocone_point.trans (he.trans (SSet.comp_const _ _).symm)
  change f = g
  apply pointJoinNerve_hom_ext hl hr
  change walkingFullJoinCocone.val.app (Opposite.op ⦋1⦌)
    (SerrePositivity.InfinityCategories.F1B.joinCoconeLegSimplex (nerveVertex walkingImage)) = _
  rw [walkingFullJoinCocone_image_leg]
  exact ComposableArrows.ext₁ rfl rfl rfl

end SerrePositivity.InfinityCategories.F2.Idempotent
