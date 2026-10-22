module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingFullCone
public import SerrePositivity.InfinityCategories.F2.Idempotent.PointJoinNerveExt

/-!
概要：元の全錐を元の分裂対象の一点へ制限すると、元の定値な一点錐になる。
方針：全写像を両境界と元の恒等脚で比較する。
規約：元の一点包含と元の全錐をそのまま制限する。
使われ方：任意の quasicategory への像で元の錐の極限性を証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全錐の始対象への一点制限は、元の分裂対象への定値な全写像。 -/
lemma walkingFullJoinCone_point_restrict :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (nervePoint walkingImage) ≫ walkingFullJoinCone.val =
      SSet.const (nerveVertex walkingImage) := by
  let f := joinMap (𝟙 (Δ[0] : SSet.{u})) (nervePoint walkingImage) ≫ walkingFullJoinCone.val
  let g : join (Δ[0] : SSet.{u}) Δ[0] ⟶ SplitShape := SSet.const (nerveVertex walkingImage)
  have he : nervePoint walkingImage =
      (SSet.const (nerveVertex walkingImage) : (Δ[0] : SSet.{u}) ⟶ SplitShape) := by
    rw [nervePoint, SSet.yonedaEquiv_symm_zero]
  have hl : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ f = joinInl _ _ ≫ g := by
    dsimp only [f, g]
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
    exact walkingFullJoinCone_point.trans (he.trans (SSet.comp_const _ _).symm)
  have hr : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ f = joinInr _ _ ≫ g := by
    dsimp only [f, g]
    rw [← Category.assoc, joinInr_joinMap, Category.assoc]
    have h := congrArg (fun q ↦ nervePoint walkingImage ≫ q) walkingFullJoinCone.property
    exact h.trans ((Category.comp_id _).trans (he.trans (SSet.comp_const _ _).symm))
  change f = g
  apply pointJoinNerve_hom_ext hl hr
  change walkingFullJoinCone.val.app (Opposite.op ⦋1⦌)
    (F1B.kanConeLegSimplex walkingImage) = _
  rw [walkingFullJoinCone_image_leg]
  exact ComposableArrows.ext₁ rfl rfl rfl

end SerrePositivity.InfinityCategories.F2.Idempotent
